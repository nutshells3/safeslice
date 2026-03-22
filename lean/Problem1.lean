import Mathlib

noncomputable section

namespace SafeSlice

abbrev Detector (C U : Type _) := C → Finset U → Prop

structure Witness (C U : Type _) where
  context : C
  premises : Finset U
  extension : Finset U
  conclusion : U
deriving DecidableEq

open Classical in
noncomputable def activeDetectors {C U : Type _}
    (B : Finset (Detector C U)) (c : C) (Γ : Finset U) : Finset (Detector C U) :=
  B.filter fun d => d c Γ

def witnessTransition {C U : Type _} [DecidableEq U]
    (derives : C → Finset U → U → Prop) (p : Witness C U) : Prop :=
  derives p.context p.premises p.conclusion ∧
    ¬ derives p.context (p.premises ∪ p.extension) p.conclusion

def detectorFlipsOn {C U : Type _} [DecidableEq U]
    (d : Detector C U) (p : Witness C U) : Prop :=
  ¬ (d p.context p.premises ↔ d p.context (p.premises ∪ p.extension))

def pairwiseDetectorDisjoint {C U : Type _} [DecidableEq U]
    (W : Finset (Witness C U)) : Prop :=
  ∀ ⦃p q : Witness C U⦄, p ∈ W → q ∈ W → p ≠ q →
    ∀ d, detectorFlipsOn d p → ¬ detectorFlipsOn d q

def detectorMonotoneAt {C U F : Type _} [DecidableEq F]
    (M : C → Finset F → Finset (Detector C U) → F → Prop) : Prop :=
  ∀ c X Y A ψ, M c X A ψ → M c (X ∪ Y) A ψ

structure FExceptionCompilation {C U F : Type _}
    [DecidableEq U] [DecidableEq F]
    (derives : C → Finset U → U → Prop)
    (family basis : Finset (Detector C U))
    (M : C → Finset F → Finset (Detector C U) → F → Prop)
    (τ : U → F) : Prop where
  basisSubset : ∀ ⦃d⦄, d ∈ basis → d ∈ family
  monotone : detectorMonotoneAt M
  simulates :
    ∀ c Γ φ, derives c Γ φ ↔ M c (Γ.image τ) (activeDetectors basis c Γ) (τ φ)

lemma activeDetectors_eq_of_stable {C U : Type _} [DecidableEq U]
    {B : Finset (Detector C U)} {p : Witness C U}
    (hStable :
      ∀ d, d ∈ B → (d p.context p.premises ↔ d p.context (p.premises ∪ p.extension))) :
    activeDetectors B p.context p.premises =
      activeDetectors B p.context (p.premises ∪ p.extension) := by
  classical
  ext d
  by_cases hd : d ∈ B
  · have hiff := hStable d hd
    simp [activeDetectors, hd, hiff]
  · simp [activeDetectors, hd]

theorem compilationWitnessNeedsDetectorFlip {C U F : Type _}
    [DecidableEq U] [DecidableEq F]
    {derives : C → Finset U → U → Prop}
    {family basis : Finset (Detector C U)}
    {M : C → Finset F → Finset (Detector C U) → F → Prop}
    {τ : U → F} {p : Witness C U}
    (comp : FExceptionCompilation derives family basis M τ)
    (hWit : witnessTransition derives p) :
    ∃ d ∈ basis, detectorFlipsOn d p := by
  classical
  rcases hWit with ⟨hPos, hNeg⟩
  by_contra hNo
  have hStable :
      ∀ d, d ∈ basis →
        (d p.context p.premises ↔ d p.context (p.premises ∪ p.extension)) := by
    intro d hd
    by_contra hFlip
    exact hNo ⟨d, hd, by simpa [detectorFlipsOn] using hFlip⟩
  have hActive :
      activeDetectors basis p.context p.premises =
        activeDetectors basis p.context (p.premises ∪ p.extension) :=
    activeDetectors_eq_of_stable hStable
  have hCompiled :
      M p.context (p.premises.image τ)
        (activeDetectors basis p.context p.premises) (τ p.conclusion) :=
    (comp.simulates _ _ _).mp hPos
  have hCompiled' :
      M p.context ((p.premises.image τ) ∪ (p.extension.image τ))
        (activeDetectors basis p.context p.premises) (τ p.conclusion) :=
    comp.monotone _ _ _ _ _ hCompiled
  have hExtended :
      M p.context ((p.premises ∪ p.extension).image τ)
        (activeDetectors basis p.context (p.premises ∪ p.extension)) (τ p.conclusion) := by
    simpa [hActive, Finset.image_union] using hCompiled'
  have : derives p.context (p.premises ∪ p.extension) p.conclusion :=
    (comp.simulates _ _ _).mpr hExtended
  exact hNeg this

open Classical in
noncomputable def chooseDetector {C U F : Type _}
    [DecidableEq U] [DecidableEq F]
    {derives : C → Finset U → U → Prop}
    {family basis : Finset (Detector C U)}
    {M : C → Finset F → Finset (Detector C U) → F → Prop}
    {τ : U → F}
    (comp : FExceptionCompilation derives family basis M τ)
    {W : Finset (Witness C U)}
    (hW : ∀ p ∈ W, witnessTransition derives p) :
    Witness C U → Detector C U
  | p =>
      if hp : p ∈ W then
        Classical.choose (compilationWitnessNeedsDetectorFlip comp (hW p hp))
      else
        fun _ _ => False

lemma chooseDetector_memBasis {C U F : Type _}
    [DecidableEq U] [DecidableEq F]
    {derives : C → Finset U → U → Prop}
    {family basis : Finset (Detector C U)}
    {M : C → Finset F → Finset (Detector C U) → F → Prop}
    {τ : U → F}
    (comp : FExceptionCompilation derives family basis M τ)
    {W : Finset (Witness C U)}
    (hW : ∀ p ∈ W, witnessTransition derives p)
    {p : Witness C U} (hp : p ∈ W) :
    chooseDetector comp hW p ∈ basis := by
  classical
  rw [chooseDetector, dif_pos hp]
  exact (Classical.choose_spec (compilationWitnessNeedsDetectorFlip comp (hW p hp))).1

lemma chooseDetector_flips {C U F : Type _}
    [DecidableEq U] [DecidableEq F]
    {derives : C → Finset U → U → Prop}
    {family basis : Finset (Detector C U)}
    {M : C → Finset F → Finset (Detector C U) → F → Prop}
    {τ : U → F}
    (comp : FExceptionCompilation derives family basis M τ)
    {W : Finset (Witness C U)}
    (hW : ∀ p ∈ W, witnessTransition derives p)
    {p : Witness C U} (hp : p ∈ W) :
    detectorFlipsOn (chooseDetector comp hW p) p := by
  classical
  rw [chooseDetector, dif_pos hp]
  exact (Classical.choose_spec (compilationWitnessNeedsDetectorFlip comp (hW p hp))).2

theorem pairwiseDetectorDisjointWitnessesNeedLargeBasis {C U F : Type _}
    [DecidableEq U] [DecidableEq F]
    {derives : C → Finset U → U → Prop}
    {family basis : Finset (Detector C U)}
    {M : C → Finset F → Finset (Detector C U) → F → Prop}
    {τ : U → F} {W : Finset (Witness C U)}
    (comp : FExceptionCompilation derives family basis M τ)
    (hW : ∀ p ∈ W, witnessTransition derives p)
    (hDisj : pairwiseDetectorDisjoint W) :
    W.card ≤ basis.card := by
  classical
  let f : Witness C U → Detector C U := chooseDetector comp hW
  have hfMaps : Set.MapsTo f (W : Set (Witness C U)) (basis : Set (Detector C U)) := by
    intro p hp
    exact chooseDetector_memBasis comp hW hp
  have hfInj : Set.InjOn f (W : Set (Witness C U)) := by
    intro p hp q hq hEq
    by_contra hNe
    have hpFlip : detectorFlipsOn (f p) p :=
      chooseDetector_flips comp hW hp
    have hqFlip : detectorFlipsOn (f q) q :=
      chooseDetector_flips comp hW hq
    have hqNo : ¬ detectorFlipsOn (f p) q :=
      hDisj hp hq hNe (f p) hpFlip
    exact hqNo (by simpa [f, hEq] using hqFlip)
  exact Finset.card_le_card_of_injOn f hfMaps hfInj

/- Concrete finite examples such as Tweety will be layered on top of the core
   lower-bound theorems once the generic detector basis API is stable. -/

end SafeSlice
