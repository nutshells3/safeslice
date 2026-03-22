from __future__ import annotations

import math
from statistics import NormalDist

from .models import BoundMethod


SUPPORTED_BOUND_METHODS = (
    BoundMethod.HOEFFDING.value,
    BoundMethod.WILSON.value,
    BoundMethod.JEFFREYS.value,
    BoundMethod.CLOPPER_PEARSON.value,
    BoundMethod.AGRESTI_COULL.value,
    BoundMethod.EMPIRICAL_BERNSTEIN.value,
)


def clip(value: float, lo: float = 0.0, hi: float = 1.0) -> float:
    return max(lo, min(hi, value))


def event_delta(confidence: float, num_slices: int, num_boundaries: int) -> float:
    total_events = max(1, num_slices + num_boundaries)
    return (1.0 - confidence) / total_events


def _apply_time_uniform_delta(delta: float, time_uniform_horizon: int | None) -> float:
    if delta <= 0.0 or delta >= 1.0:
        raise ValueError(f"delta must lie in (0, 1), got {delta!r}")
    if time_uniform_horizon is None:
        return delta
    horizon = max(1, int(time_uniform_horizon))
    return delta / horizon


def hoeffding_radius(samples: int, delta: float) -> float:
    if samples <= 0:
        return 1.0
    return math.sqrt(math.log(2.0 / delta) / (2.0 * samples))


def _two_sided_z(delta: float) -> float:
    if delta <= 0.0 or delta >= 1.0:
        raise ValueError(f"delta must lie in (0, 1), got {delta!r}")
    return NormalDist().inv_cdf(1.0 - (delta / 2.0))


def _log_beta(a: float, b: float) -> float:
    return math.lgamma(a) + math.lgamma(b) - math.lgamma(a + b)


def _betacf(a: float, b: float, x: float) -> float:
    max_iter = 200
    eps = 3.0e-14
    fpmin = 1.0e-300

    qab = a + b
    qap = a + 1.0
    qam = a - 1.0

    c = 1.0
    d = 1.0 - (qab * x / qap)
    if abs(d) < fpmin:
        d = fpmin
    d = 1.0 / d
    h = d

    for m in range(1, max_iter + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        if abs(d) < fpmin:
            d = fpmin
        c = 1.0 + aa / c
        if abs(c) < fpmin:
            c = fpmin
        d = 1.0 / d
        h *= d * c

        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        if abs(d) < fpmin:
            d = fpmin
        c = 1.0 + aa / c
        if abs(c) < fpmin:
            c = fpmin
        d = 1.0 / d
        delta_h = d * c
        h *= delta_h

        if abs(delta_h - 1.0) < eps:
            break

    return h


def regularized_beta(x: float, a: float, b: float) -> float:
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    if a <= 0.0 or b <= 0.0:
        raise ValueError("Beta parameters must be positive.")

    log_front = a * math.log(x) + b * math.log1p(-x) - _log_beta(a, b)
    front = math.exp(log_front)

    if x < (a + 1.0) / (a + b + 2.0):
        return front * _betacf(a, b, x) / a
    return 1.0 - (front * _betacf(b, a, 1.0 - x) / b)


def beta_quantile(probability: float, a: float, b: float) -> float:
    if probability <= 0.0:
        return 0.0
    if probability >= 1.0:
        return 1.0

    lo = 0.0
    hi = 1.0
    for _ in range(80):
        mid = (lo + hi) / 2.0
        cdf = regularized_beta(mid, a, b)
        if cdf < probability:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2.0


def wilson_interval(successes: int, samples: int, delta: float) -> tuple[float, float]:
    if samples <= 0:
        return 0.0, 1.0
    success_rate_hat = successes / samples
    z = _two_sided_z(delta)
    z2 = z * z
    denom = 1.0 + (z2 / samples)
    center = (success_rate_hat + (z2 / (2.0 * samples))) / denom
    margin = (
        z
        * math.sqrt(
            (success_rate_hat * (1.0 - success_rate_hat) / samples)
            + (z2 / (4.0 * samples * samples))
        )
        / denom
    )
    return clip(center - margin), clip(center + margin)


def agresti_coull_interval(successes: int, samples: int, delta: float) -> tuple[float, float]:
    if samples <= 0:
        return 0.0, 1.0
    z = _two_sided_z(delta)
    z2 = z * z
    adjusted_samples = samples + z2
    adjusted_rate = (successes + (z2 / 2.0)) / adjusted_samples
    margin = z * math.sqrt(adjusted_rate * (1.0 - adjusted_rate) / adjusted_samples)
    return clip(adjusted_rate - margin), clip(adjusted_rate + margin)


def jeffreys_interval(successes: int, samples: int, delta: float) -> tuple[float, float]:
    if samples <= 0:
        return 0.0, 1.0
    lower = beta_quantile(delta / 2.0, successes + 0.5, samples - successes + 0.5)
    upper = beta_quantile(1.0 - (delta / 2.0), successes + 0.5, samples - successes + 0.5)
    return clip(lower), clip(upper)


def clopper_pearson_interval(successes: int, samples: int, delta: float) -> tuple[float, float]:
    if samples <= 0:
        return 0.0, 1.0
    if successes <= 0:
        lower = 0.0
    else:
        lower = beta_quantile(delta / 2.0, successes, samples - successes + 1.0)
    if successes >= samples:
        upper = 1.0
    else:
        upper = beta_quantile(1.0 - (delta / 2.0), successes + 1.0, samples - successes)
    return clip(lower), clip(upper)


def empirical_bernstein_radius(successes: int, samples: int, delta: float) -> float:
    if samples <= 1:
        return 1.0
    if delta <= 0.0 or delta >= 1.0:
        raise ValueError(f"delta must lie in (0, 1), got {delta!r}")
    success_rate_hat = successes / samples
    sample_variance = (samples / (samples - 1.0)) * success_rate_hat * (1.0 - success_rate_hat)
    log_term = math.log(3.0 / delta)
    radius = math.sqrt((2.0 * sample_variance * log_term) / samples) + (3.0 * log_term / samples)
    return min(1.0, radius)


def slice_bounds(
    successes: int,
    samples: int,
    *,
    oracle_error: float,
    delta_event: float,
    bound_method: str = "hoeffding",
    time_uniform_horizon: int | None = None,
) -> tuple[float, float, float, float, float]:
    success_rate_hat = successes / samples if samples else 0.0
    method = str(bound_method)
    effective_delta = _apply_time_uniform_delta(delta_event, time_uniform_horizon)

    if method == BoundMethod.HOEFFDING.value:
        sample_radius = hoeffding_radius(samples, effective_delta)
        total_radius = oracle_error + sample_radius
        lower_bound = clip(success_rate_hat - total_radius)
        upper_bound = clip(success_rate_hat + total_radius)
        return success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound

    if method == BoundMethod.WILSON.value:
        lower_sampling_bound, upper_sampling_bound = wilson_interval(successes, samples, effective_delta)
        sample_radius = max(
            success_rate_hat - lower_sampling_bound,
            upper_sampling_bound - success_rate_hat,
        )
        lower_bound = clip(lower_sampling_bound - oracle_error)
        upper_bound = clip(upper_sampling_bound + oracle_error)
        total_radius = max(success_rate_hat - lower_bound, upper_bound - success_rate_hat)
        return success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound

    if method == BoundMethod.JEFFREYS.value:
        lower_sampling_bound, upper_sampling_bound = jeffreys_interval(successes, samples, effective_delta)
        sample_radius = max(
            success_rate_hat - lower_sampling_bound,
            upper_sampling_bound - success_rate_hat,
        )
        lower_bound = clip(lower_sampling_bound - oracle_error)
        upper_bound = clip(upper_sampling_bound + oracle_error)
        total_radius = max(success_rate_hat - lower_bound, upper_bound - success_rate_hat)
        return success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound

    if method == BoundMethod.CLOPPER_PEARSON.value:
        lower_sampling_bound, upper_sampling_bound = clopper_pearson_interval(successes, samples, effective_delta)
        sample_radius = max(
            success_rate_hat - lower_sampling_bound,
            upper_sampling_bound - success_rate_hat,
        )
        lower_bound = clip(lower_sampling_bound - oracle_error)
        upper_bound = clip(upper_sampling_bound + oracle_error)
        total_radius = max(success_rate_hat - lower_bound, upper_bound - success_rate_hat)
        return success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound

    if method == BoundMethod.AGRESTI_COULL.value:
        lower_sampling_bound, upper_sampling_bound = agresti_coull_interval(successes, samples, effective_delta)
        sample_radius = max(
            success_rate_hat - lower_sampling_bound,
            upper_sampling_bound - success_rate_hat,
        )
        lower_bound = clip(lower_sampling_bound - oracle_error)
        upper_bound = clip(upper_sampling_bound + oracle_error)
        total_radius = max(success_rate_hat - lower_bound, upper_bound - success_rate_hat)
        return success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound

    if method == BoundMethod.EMPIRICAL_BERNSTEIN.value:
        sample_radius = empirical_bernstein_radius(successes, samples, effective_delta)
        total_radius = oracle_error + sample_radius
        lower_bound = clip(success_rate_hat - total_radius)
        upper_bound = clip(success_rate_hat + total_radius)
        return success_rate_hat, sample_radius, total_radius, lower_bound, upper_bound

    raise ValueError(
        f"Unsupported bound_method: {bound_method}. "
        f"Supported methods: {', '.join(SUPPORTED_BOUND_METHODS)}"
    )


def drop_bounds(
    left_success_rate_hat: float,
    right_success_rate_hat: float,
    *,
    left_lower_bound: float,
    left_upper_bound: float,
    right_lower_bound: float,
    right_upper_bound: float,
) -> tuple[float, float, float, float]:
    drop_hat = left_success_rate_hat - right_success_rate_hat
    drop_lower_bound = left_lower_bound - right_upper_bound
    drop_upper_bound = left_upper_bound - right_lower_bound
    drop_radius = max(drop_hat - drop_lower_bound, drop_upper_bound - drop_hat)
    return drop_hat, drop_radius, drop_lower_bound, drop_upper_bound


def enough_precision(total_radius: float, target_half_width: float) -> bool:
    return total_radius <= target_half_width
