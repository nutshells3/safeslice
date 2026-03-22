from __future__ import annotations

from typing import FrozenSet, Protocol, Sequence

from .models import ChainSpec, CheckerResult, SliceSpec, TaskSpec


class PromptRenderer(Protocol):
    def render(self, chain: ChainSpec, slice_spec: SliceSpec) -> str:
        """Render the concrete prompt for one slice experiment."""


class Sampler(Protocol):
    def sample(self, chain: ChainSpec, slice_spec: SliceSpec, prompt: str) -> str:
        """Draw one model sample for the given chain slice."""


class Checker(Protocol):
    def check(self, output_text: str, chain: ChainSpec, slice_spec: SliceSpec) -> CheckerResult:
        """Return success or failure for a sampled model output."""


class QuestionFamily(Protocol):
    def questions(self, active_keys: FrozenSet[str]) -> Sequence[str]:
        """Enumerate binary clarification questions available at this state."""

    def split(
        self, active_keys: FrozenSet[str], question_id: str
    ) -> tuple[FrozenSet[str], FrozenSet[str]]:
        """Split the active hidden-key support by a binary question."""

    def render(self, question_id: str, task: TaskSpec) -> str:
        """Render the human-facing clarification prompt for a question."""
