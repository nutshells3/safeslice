import Mathlib

noncomputable section

open scoped BigOperators

namespace SafeSlice

section Benchmark

variable {K : Type _}

/-- Prior mass carried by a finite key cell. -/
def mass (μ : K → NNRat) (S : Finset K) : NNRat :=
  S.sum μ

/-- Feasible representative sets under an unconstrained `slots`-way clarification budget. -/
def feasibleSubsets (slots : Nat) (keys : Finset K) : Finset (Finset K) :=
  keys.powerset.filter fun S => S.card ≤ slots

/-- Unconstrained benchmark success: choose at most `slots` keys
and collect their total prior mass. -/
def succAll (slots : Nat) (μ : K → NNRat) (keys : Finset K) : NNRat :=
  (feasibleSubsets slots keys).sup (mass μ)

/-- Pick a key of maximal prior mass from a nonempty key set. -/
noncomputable def greedyChoice (μ : K → NNRat) (keys : Finset K) (hkeys : keys.Nonempty) : K :=
  by
    classical
    exact Classical.choose (Finset.exists_max_image keys μ hkeys)

lemma greedyChoice_mem (μ : K → NNRat) (keys : Finset K) (hkeys : keys.Nonempty) :
    greedyChoice μ keys hkeys ∈ keys := by
  classical
  exact (Classical.choose_spec (Finset.exists_max_image keys μ hkeys)).1

lemma le_greedyChoice (μ : K → NNRat) (keys : Finset K) (hkeys : keys.Nonempty) :
    ∀ x ∈ keys, μ x ≤ μ (greedyChoice μ keys hkeys) := by
  classical
  exact (Classical.choose_spec (Finset.exists_max_image keys μ hkeys)).2

variable [DecidableEq K]

/-- Greedy selection of the `slots` heaviest keys.
This is extensionally the top-`slots` mass set. -/
noncomputable def topSubset (μ : K → NNRat) : Nat → Finset K → Finset K
  | 0, _ => ∅
  | slots + 1, keys =>
      if hkeys : keys.Nonempty then
        let k := greedyChoice μ keys hkeys
        insert k (topSubset μ slots (keys.erase k))
      else
        ∅

/-- The exact sum of the `slots` largest masses in `keys`, defined by greedy extraction. -/
def topMass (μ : K → NNRat) (slots : Nat) (keys : Finset K) : NNRat :=
  mass μ (topSubset μ slots keys)

omit [DecidableEq K] in
@[simp] lemma mass_empty {μ : K → NNRat} : mass μ ∅ = 0 := by
  simp [mass]

omit [DecidableEq K] in
@[simp] lemma mass_singleton {μ : K → NNRat} {k : K} : mass μ ({k} : Finset K) = μ k := by
  simp [mass]

omit [DecidableEq K] in
lemma mass_mono {μ : K → NNRat} {S T : Finset K} (hST : S ⊆ T) :
    mass μ S ≤ mass μ T := by
  simpa [mass] using (Finset.sum_le_sum_of_subset hST : S.sum μ ≤ T.sum μ)

lemma mass_insert {μ : K → NNRat} {k : K} {S : Finset K} (hk : k ∉ S) :
    mass μ (insert k S) = μ k + mass μ S := by
  simpa [mass] using (Finset.sum_insert hk (f := μ))

lemma mass_eq_mass_erase_add {μ : K → NNRat} {k : K} {S : Finset K} (hk : k ∈ S) :
    mass μ S = μ k + mass μ (S.erase k) := by
  simpa [mass, add_comm, add_left_comm, add_assoc] using (Finset.sum_erase_add S μ hk).symm

lemma topSubset_subset (μ : K → NNRat) :
    ∀ slots keys, topSubset μ slots keys ⊆ keys
  | 0, keys => by
      simp [topSubset]
  | slots + 1, keys => by
      classical
      by_cases hkeys : keys.Nonempty
      · let k := greedyChoice μ keys hkeys
        intro x hx
        have hx' : x = k ∨ x ∈ topSubset μ slots (keys.erase k) := by
          simpa [topSubset, hkeys, k] using hx
        rcases hx' with rfl | hx
        · exact greedyChoice_mem μ keys hkeys
        · exact Finset.mem_of_mem_erase ((topSubset_subset μ slots (keys.erase k)) hx)
      · simp [topSubset, hkeys]

lemma topSubset_card_le (μ : K → NNRat) :
    ∀ slots keys, (topSubset μ slots keys).card ≤ slots
  | 0, keys => by
      simp [topSubset]
  | slots + 1, keys => by
      classical
      by_cases hkeys : keys.Nonempty
      · let k := greedyChoice μ keys hkeys
        have hk_not_mem : k ∉ topSubset μ slots (keys.erase k) := by
          intro hk
          exact (by simp : k ∉ keys.erase k) ((topSubset_subset μ slots (keys.erase k)) hk)
        simp [topSubset, hkeys, k, hk_not_mem, topSubset_card_le μ slots (keys.erase k)]
      · simp [topSubset, hkeys]

lemma topMass_succ_nonempty {μ : K → NNRat} {slots : Nat} {keys : Finset K}
    (hkeys : keys.Nonempty) :
    topMass μ (slots + 1) keys =
      μ (greedyChoice μ keys hkeys) +
        topMass μ slots (keys.erase (greedyChoice μ keys hkeys)) := by
  classical
  let k := greedyChoice μ keys hkeys
  have hk_not_mem : k ∉ topSubset μ slots (keys.erase k) := by
    intro hk
    exact (by simp : k ∉ keys.erase k) ((topSubset_subset μ slots (keys.erase k)) hk)
  simp [topMass, topSubset, hkeys, k, mass_insert, hk_not_mem]

lemma topSubset_mem_feasible (μ : K → NNRat) (slots : Nat) (keys : Finset K) :
    topSubset μ slots keys ∈ feasibleSubsets slots keys := by
  refine Finset.mem_filter.mpr ?_
  exact ⟨Finset.mem_powerset.mpr (topSubset_subset μ slots keys), topSubset_card_le μ slots keys⟩

lemma mass_le_topMass_of_card_le {μ : K → NNRat} :
    ∀ {slots : Nat} {keys S : Finset K},
      S ⊆ keys →
      S.card ≤ slots →
      mass μ S ≤ topMass μ slots keys
  | 0, keys, S, hSK, hCard => by
      have hZero : S.card = 0 := Nat.eq_zero_of_le_zero hCard
      have hEmpty : S = ∅ := Finset.card_eq_zero.mp hZero
      subst hEmpty
      simp [topMass, topSubset, mass]
  | slots + 1, keys, S, hSK, hCard => by
      classical
      by_cases hkeys : keys.Nonempty
      · let k := greedyChoice μ keys hkeys
        by_cases hkS : k ∈ S
        · have hEraseSubset : S.erase k ⊆ keys.erase k := by
            intro x hx
            have hxS : x ∈ S := Finset.mem_of_mem_erase hx
            have hxK : x ∈ keys := hSK hxS
            exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hxK⟩
          have hEraseCard : (S.erase k).card ≤ slots := by
            rw [Finset.card_erase_of_mem hkS]
            omega
          calc
            mass μ S = μ k + mass μ (S.erase k) := mass_eq_mass_erase_add hkS
            _ ≤ μ k + topMass μ slots (keys.erase k) := by
              gcongr
              exact mass_le_topMass_of_card_le hEraseSubset hEraseCard
            _ = topMass μ (slots + 1) keys := by
              simpa [k] using
                (topMass_succ_nonempty (μ := μ) (slots := slots) (keys := keys) hkeys).symm
        · by_cases hS : S.Nonempty
          · obtain ⟨x, hxS⟩ := hS
            have hxK : x ∈ keys := hSK hxS
            have hEraseSubset : S.erase x ⊆ keys.erase k := by
              intro y hy
              have hyS : y ∈ S := Finset.mem_of_mem_erase hy
              have hyK : y ∈ keys := hSK hyS
              have hyNotK : y ≠ k := by
                intro hEq
                exact hkS (hEq ▸ hyS)
              exact Finset.mem_erase.mpr ⟨hyNotK, hyK⟩
            have hEraseCard : (S.erase x).card ≤ slots := by
              rw [Finset.card_erase_of_mem hxS]
              omega
            have hxMax : μ x ≤ μ k := by
              simpa [k] using le_greedyChoice μ keys hkeys x hxK
            calc
              mass μ S = μ x + mass μ (S.erase x) := mass_eq_mass_erase_add hxS
              _ ≤ μ k + topMass μ slots (keys.erase k) := by
                gcongr
                exact mass_le_topMass_of_card_le hEraseSubset hEraseCard
              _ = topMass μ (slots + 1) keys := by
                simpa [k] using
                  (topMass_succ_nonempty (μ := μ) (slots := slots) (keys := keys) hkeys).symm
          · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
            subst hEmpty
            simp [mass]
      · have hEmptyKeys : keys = ∅ := Finset.not_nonempty_iff_eq_empty.mp hkeys
        have hEmptyS : S = ∅ := by
          ext x
          constructor
          · intro hx
            exfalso
            simpa [hEmptyKeys] using hSK hx
          · intro hx
            cases hx
        subst hEmptyKeys
        subst hEmptyS
        simp [mass]

/-- Exact benchmark theorem: unrestricted clarification is exactly the sum of the top `slots`
prior masses. -/
theorem succAll_eq_topMass (μ : K → NNRat) (slots : Nat) (keys : Finset K) :
    succAll slots μ keys = topMass μ slots keys := by
  apply le_antisymm
  · rw [succAll, Finset.sup_le_iff]
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hPow, hCard⟩
    exact mass_le_topMass_of_card_le (μ := μ) (Finset.mem_powerset.mp hPow) hCard
  · rw [succAll, topMass]
    exact Finset.le_sup (topSubset_mem_feasible μ slots keys)

omit [DecidableEq K] in
theorem succAll_eq_totalMass_of_card_le (μ : K → NNRat) {slots : Nat} {keys : Finset K}
    (hSlots : keys.card ≤ slots) :
    succAll slots μ keys = mass μ keys := by
  apply le_antisymm
  · rw [succAll, Finset.sup_le_iff]
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hPow, _⟩
    exact mass_mono (μ := μ) (Finset.mem_powerset.mp hPow)
  · rw [succAll]
    exact Finset.le_sup <| Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (subset_rfl), hSlots⟩

/-- With `q` binary clarifications, the unconstrained benchmark has `2^q` cells available. -/
def succQuestions (questions : Nat) (μ : K → NNRat) (keys : Finset K) : NNRat :=
  succAll (2 ^ questions) μ keys

lemma card_le_twoPow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hOne : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      calc
        n + 1 ≤ 2 ^ n + 1 := by omega
        _ ≤ 2 ^ n + 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [← two_mul, pow_succ, Nat.mul_comm]

omit [DecidableEq K] in
theorem succQuestions_card_eq_totalMass (μ : K → NNRat) (keys : Finset K) :
    succQuestions keys.card μ keys = mass μ keys := by
  simpa [succQuestions] using
    succAll_eq_totalMass_of_card_le
      (μ := μ) (keys := keys) (slots := 2 ^ keys.card) (card_le_twoPow keys.card)

omit [DecidableEq K] in
theorem succQuestions_zero_eq_singleShot (μ : K → NNRat) (keys : Finset K) :
    succQuestions 0 μ keys = keys.sup μ := by
  classical
  by_cases hkeys : keys.Nonempty
  · let k := greedyChoice μ keys hkeys
    have hkMem : k ∈ keys := by simpa [k] using greedyChoice_mem μ keys hkeys
    have hkMax : ∀ x ∈ keys, μ x ≤ μ k := by
      intro x hx
      simpa [k] using le_greedyChoice μ keys hkeys x hx
    have hSup : keys.sup μ = μ k := by
      apply le_antisymm
      · exact Finset.sup_le_iff.mpr hkMax
      · exact Finset.le_sup hkMem
    have hTop : topMass μ 1 keys = μ k := by
      simp [topMass, topSubset, hkeys, k, mass]
    calc
      succQuestions 0 μ keys = topMass μ 1 keys := by
        simpa [succQuestions] using succAll_eq_topMass (μ := μ) 1 keys
      _ = μ k := hTop
      _ = keys.sup μ := hSup.symm
  · have hEmpty : keys = ∅ := Finset.not_nonempty_iff_eq_empty.mp hkeys
    subst hEmpty
    simp [succQuestions, succAll, feasibleSubsets, mass]

omit [DecidableEq K] in
theorem exists_question_budget {μ : K → NNRat} {keys : Finset K} {target : NNRat}
    (hTarget : target ≤ mass μ keys) :
    ∃ q, target ≤ succQuestions q μ keys := by
  refine ⟨keys.card, ?_⟩
  calc
    target ≤ mass μ keys := hTarget
    _ = succQuestions keys.card μ keys := (succQuestions_card_eq_totalMass (μ := μ) keys).symm

/-- Minimal question budget forced by the unrestricted benchmark. -/
noncomputable def qBench (μ : K → NNRat) (keys : Finset K) (target : NNRat)
    (hTarget : target ≤ mass μ keys) : Nat :=
  Nat.find (exists_question_budget (μ := μ) (keys := keys) hTarget)

omit [DecidableEq K] in
theorem qBench_spec {μ : K → NNRat} {keys : Finset K} {target : NNRat}
    (hTarget : target ≤ mass μ keys) :
    target ≤ succQuestions (qBench μ keys target hTarget) μ keys := by
  exact Nat.find_spec (exists_question_budget (μ := μ) (keys := keys) hTarget)

omit [DecidableEq K] in
theorem qBench_min {μ : K → NNRat} {keys : Finset K} {target : NNRat}
    (hTarget : target ≤ mass μ keys) {q : Nat}
    (hq : q < qBench μ keys target hTarget) :
    succQuestions q μ keys < target := by
  by_contra hNot
  have hHit : target ≤ succQuestions q μ keys := le_of_not_gt hNot
  have hMin : qBench μ keys target hTarget ≤ q :=
    Nat.find_min' (exists_question_budget (μ := μ) (keys := keys) hTarget) hHit
  exact Nat.not_lt_of_ge hMin hq

/- Any restricted question family that succeeds in `q` rounds
must beat the benchmark lower bound `qBench`. -/
omit [DecidableEq K] in
theorem qBench_le_of_achieves_target {μ : K → NNRat} {keys : Finset K} {target : NNRat}
    (hTarget : target ≤ mass μ keys)
    {succQ : Nat → NNRat}
    (hUpper : ∀ q, succQ q ≤ succQuestions q μ keys)
    {q : Nat} (hAchieves : target ≤ succQ q) :
    qBench μ keys target hTarget ≤ q := by
  exact Nat.find_min' (exists_question_budget (μ := μ) (keys := keys) hTarget) <|
    le_trans hAchieves (hUpper q)

end Benchmark

section SortedMasses

variable {K : Type _} [DecidableEq K]

/-- The descending greedy list of masses obtained by repeatedly removing a current heaviest key. -/
noncomputable def sortedMassesAux (μ : K → NNRat) : Nat → Finset K → List NNRat
  | 0, _ => []
  | fuel + 1, keys =>
      if hkeys : keys.Nonempty then
        let k := greedyChoice μ keys hkeys
        μ k :: sortedMassesAux μ fuel (keys.erase k)
      else
        []

/-- The full descending greedy mass list for a finite key set. -/
noncomputable def sortedMasses (μ : K → NNRat) (keys : Finset K) : List NNRat :=
  sortedMassesAux μ keys.card keys

@[simp] lemma sortedMassesAux_succ_nonempty
    (μ : K → NNRat) (fuel : Nat) (keys : Finset K) (hkeys : keys.Nonempty) :
    sortedMassesAux μ (fuel + 1) keys =
      μ (greedyChoice μ keys hkeys) ::
        sortedMassesAux μ fuel (keys.erase (greedyChoice μ keys hkeys)) := by
  simp [sortedMassesAux, hkeys]

@[simp] lemma sortedMassesAux_succ_empty
    (μ : K → NNRat) (fuel : Nat) (keys : Finset K) (hkeys : ¬ keys.Nonempty) :
    sortedMassesAux μ (fuel + 1) keys = [] := by
  simp [sortedMassesAux, hkeys]

lemma take_sortedMassesAux_sum_eq_topMass (μ : K → NNRat) :
    ∀ slots fuel keys,
      keys.card ≤ fuel →
        ((sortedMassesAux μ fuel keys).take slots).sum = topMass μ slots keys
  | 0, fuel, keys, hFuel => by
      simp [topMass, topSubset]
  | slots + 1, 0, keys, hFuel => by
      have hEmpty : keys = (∅ : Finset K) :=
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hFuel)
      subst hEmpty
      simp [sortedMassesAux, topMass, topSubset]
  | slots + 1, fuel + 1, keys, hFuel => by
      classical
      by_cases hkeys : keys.Nonempty
      · have hEraseFuel :
            (keys.erase (greedyChoice μ keys hkeys)).card ≤ fuel := by
          rw [Finset.card_erase_of_mem (greedyChoice_mem μ keys hkeys)]
          have hCardPos : 0 < keys.card := Finset.card_pos.mpr hkeys
          omega
        calc
          ((sortedMassesAux μ (fuel + 1) keys).take (slots + 1)).sum
              = μ (greedyChoice μ keys hkeys) +
                  ((sortedMassesAux μ fuel
                    (keys.erase (greedyChoice μ keys hkeys))).take slots).sum := by
                  simp [sortedMassesAux, hkeys]
          _ = μ (greedyChoice μ keys hkeys) +
                topMass μ slots (keys.erase (greedyChoice μ keys hkeys)) := by
                  rw [take_sortedMassesAux_sum_eq_topMass μ slots fuel
                    (keys.erase (greedyChoice μ keys hkeys)) hEraseFuel]
          _ = topMass μ (slots + 1) keys := by
                symm
                simpa using
                  topMass_succ_nonempty (μ := μ) (slots := slots) (keys := keys) hkeys
      · have hEmpty : keys = ∅ := Finset.not_nonempty_iff_eq_empty.mp hkeys
        subst hEmpty
        simp [sortedMassesAux, topMass, topSubset, hkeys]

theorem take_sortedMasses_sum_eq_topMass (μ : K → NNRat) (slots : Nat) (keys : Finset K) :
    ((sortedMasses μ keys).take slots).sum = topMass μ slots keys := by
  unfold sortedMasses
  exact take_sortedMassesAux_sum_eq_topMass μ slots keys.card keys le_rfl

theorem succAll_eq_take_sortedMasses_sum (μ : K → NNRat) (slots : Nat) (keys : Finset K) :
    succAll slots μ keys = ((sortedMasses μ keys).take slots).sum := by
  rw [succAll_eq_topMass]
  symm
  exact take_sortedMasses_sum_eq_topMass μ slots keys

theorem succQuestions_eq_take_sortedMasses_sum
    (μ : K → NNRat) (questions : Nat) (keys : Finset K) :
    succQuestions questions μ keys =
      ((sortedMasses μ keys).take (2 ^ questions)).sum := by
  simpa [succQuestions] using
    succAll_eq_take_sortedMasses_sum (μ := μ) (slots := 2 ^ questions) keys

end SortedMasses

section Restricted

variable {K Q : Type _}

/-- A restricted clarification family is determined by the binary questions
it can ask about keys. -/
structure QuestionFamily (K Q : Type _) where
  ask : Q → K → Bool

/-- A finite adaptive clarification tree over questions from `Q`. Adaptivity is represented by the
tree shape itself: each node stores the next question for the current transcript-prefix. -/
inductive Protocol (Q : Type _)
  | leaf
  | node (question : Q) (left right : Protocol Q)
deriving DecidableEq

namespace QuestionFamily

def falseCell (family : QuestionFamily K Q) (question : Q) (keys : Finset K) : Finset K :=
  keys.filter fun k => family.ask question k = false

def trueCell (family : QuestionFamily K Q) (question : Q) (keys : Finset K) : Finset K :=
  keys.filter fun k => family.ask question k = true

lemma falseCell_subset (family : QuestionFamily K Q) (question : Q) (keys : Finset K) :
    family.falseCell question keys ⊆ keys := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma trueCell_subset (family : QuestionFamily K Q) (question : Q) (keys : Finset K) :
    family.trueCell question keys ⊆ keys := by
  intro k hk
  exact (Finset.mem_filter.mp hk).1

lemma false_true_disjoint (family : QuestionFamily K Q) (question : Q) (keys : Finset K) :
    Disjoint (family.falseCell question keys) (family.trueCell question keys) := by
  refine Finset.disjoint_left.mpr ?_
  intro k hkFalse hkTrue
  have hFalse : family.ask question k = false := (Finset.mem_filter.mp hkFalse).2
  have hTrue : family.ask question k = true := (Finset.mem_filter.mp hkTrue).2
  have : false = true := hFalse.symm.trans hTrue
  cases this

end QuestionFamily

namespace Protocol

def depth : Protocol Q → Nat
  | leaf => 0
  | node _ left right => Nat.succ (max left.depth right.depth)

def leafCount : Protocol Q → Nat
  | leaf => 1
  | node _ left right => left.leafCount + right.leafCount

def cells (family : QuestionFamily K Q) : Protocol Q → Finset K → List (Finset K)
  | leaf, keys => [keys]
  | node question left right, keys =>
      cells family left (family.falseCell question keys) ++
        cells family right (family.trueCell question keys)

def success (family : QuestionFamily K Q) (μ : K → NNRat) : Protocol Q → Finset K → NNRat
  | leaf, keys => keys.sup μ
  | node question left right, keys =>
      success family μ left (family.falseCell question keys) +
        success family μ right (family.trueCell question keys)

lemma twoPow_mono {a b : Nat} (hab : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  by_contra h
  have hlt : 2 ^ b < 2 ^ a := lt_of_not_ge h
  have : b < a := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  exact Nat.not_lt_of_ge hab this

lemma leafCount_le_twoPowDepth : ∀ protocol : Protocol Q, protocol.leafCount ≤ 2 ^ protocol.depth
  | leaf => by simp [leafCount, depth]
  | node _ left right => by
      have hLeft : 2 ^ left.depth ≤ 2 ^ max left.depth right.depth :=
        twoPow_mono (le_max_left _ _)
      have hRight : 2 ^ right.depth ≤ 2 ^ max left.depth right.depth :=
        twoPow_mono (le_max_right _ _)
      calc
        (node _ left right).leafCount = left.leafCount + right.leafCount := by simp [leafCount]
        _ ≤ 2 ^ left.depth + 2 ^ right.depth := by
              gcongr <;> exact leafCount_le_twoPowDepth _
        _ ≤ 2 ^ max left.depth right.depth + 2 ^ max left.depth right.depth := by
              exact add_le_add hLeft hRight
        _ = 2 ^ (Nat.succ (max left.depth right.depth)) := by
              rw [← two_mul, pow_succ, Nat.mul_comm]
        _ = 2 ^ (node _ left right).depth := by simp [depth]

theorem exists_representatives (family : QuestionFamily K Q) (μ : K → NNRat) :
    ∀ protocol keys,
      ∃ reps : Finset K,
        reps ⊆ keys ∧
        reps.card ≤ protocol.leafCount ∧
        success family μ protocol keys ≤ mass μ reps
  | leaf, keys => by
      classical
      refine ⟨topSubset μ 1 keys, topSubset_subset μ 1 keys, ?_, ?_⟩
      · simpa [leafCount] using topSubset_card_le μ 1 keys
      · exact le_of_eq <| by
          calc
            success family μ leaf keys = keys.sup μ := by simp [success]
            _ = succQuestions 0 μ keys := (succQuestions_zero_eq_singleShot (μ := μ) keys).symm
            _ = succAll 1 μ keys := by simp [succQuestions]
            _ = topMass μ 1 keys := succAll_eq_topMass (μ := μ) 1 keys
            _ = mass μ (topSubset μ 1 keys) := rfl
  | node question left right, keys => by
      classical
      obtain ⟨leftReps, hLeftSub, hLeftCard, hLeftMass⟩ :=
        exists_representatives family μ left (family.falseCell question keys)
      obtain ⟨rightReps, hRightSub, hRightCard, hRightMass⟩ :=
        exists_representatives family μ right (family.trueCell question keys)
      have hDisj : Disjoint leftReps rightReps := by
        refine Finset.disjoint_left.mpr ?_
        intro k hkLeft hkRight
        have hkFalse : k ∈ family.falseCell question keys := hLeftSub hkLeft
        have hkTrue : k ∈ family.trueCell question keys := hRightSub hkRight
        exact (Finset.disjoint_left.mp (family.false_true_disjoint question keys) hkFalse) hkTrue
      refine ⟨leftReps ∪ rightReps, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_union.mp hk with hk | hk
        · exact family.falseCell_subset question keys (hLeftSub hk)
        · exact family.trueCell_subset question keys (hRightSub hk)
      · calc
          (leftReps ∪ rightReps).card = leftReps.card + rightReps.card :=
            Finset.card_union_of_disjoint hDisj
          _ ≤ left.leafCount + right.leafCount := by omega
          _ = (node question left right).leafCount := by simp [leafCount]
      · calc
          success family μ (node question left right) keys
              = success family μ left (family.falseCell question keys) +
                  success family μ right (family.trueCell question keys) := by
                      simp [success]
          _ ≤ mass μ leftReps + mass μ rightReps := by
                gcongr
          _ = mass μ (leftReps ∪ rightReps) := by
                symm
                simpa [mass] using Finset.sum_union hDisj (f := μ)

theorem success_le_succAll_leafCount (family : QuestionFamily K Q) (μ : K → NNRat)
    (protocol : Protocol Q) (keys : Finset K) :
    success family μ protocol keys ≤ succAll protocol.leafCount μ keys := by
  obtain ⟨reps, hSub, hCard, hMass⟩ := exists_representatives family μ protocol keys
  calc
    success family μ protocol keys ≤ mass μ reps := hMass
    _ ≤ succAll protocol.leafCount μ keys := by
          rw [succAll]
          exact Finset.le_sup <| Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr hSub, hCard⟩

theorem success_le_succQuestions (family : QuestionFamily K Q) (μ : K → NNRat)
    (protocol : Protocol Q) (keys : Finset K) :
    success family μ protocol keys ≤ succQuestions protocol.depth μ keys := by
  calc
    success family μ protocol keys ≤ succAll protocol.leafCount μ keys :=
      success_le_succAll_leafCount family μ protocol keys
    _ ≤ succAll (2 ^ protocol.depth) μ keys := by
          rw [succAll]
          apply Finset.sup_le_iff.mpr
          intro reps hReps
          rcases Finset.mem_filter.mp hReps with ⟨hPow, hCard⟩
          exact Finset.le_sup <| Finset.mem_filter.mpr
            ⟨hPow, le_trans hCard (leafCount_le_twoPowDepth protocol)⟩
    _ = succQuestions protocol.depth μ keys := rfl

end Protocol

section OptimalRestricted

variable {K Q : Type _} [Fintype Q] [DecidableEq Q]

/-- Monotonicity of the unconstrained benchmark in the representative budget. -/
theorem succAll_mono_slots (μ : K → NNRat) (keys : Finset K) {slots₁ slots₂ : Nat}
    (hSlots : slots₁ ≤ slots₂) :
    succAll slots₁ μ keys ≤ succAll slots₂ μ keys := by
  rw [succAll]
  apply Finset.sup_le_iff.mpr
  intro reps hReps
  rcases Finset.mem_filter.mp hReps with ⟨hPow, hCard⟩
  exact Finset.le_sup <| Finset.mem_filter.mpr ⟨hPow, le_trans hCard hSlots⟩

/-- Monotonicity of the question benchmark in the clarification depth. -/
theorem succQuestions_mono (μ : K → NNRat) (keys : Finset K) {q₁ q₂ : Nat}
    (hq : q₁ ≤ q₂) :
    succQuestions q₁ μ keys ≤ succQuestions q₂ μ keys := by
  rw [succQuestions, succQuestions]
  exact succAll_mono_slots μ keys (Protocol.twoPow_mono hq)

/-- Finite search space of adaptive protocols using only questions from `Q` up to depth `q`. -/
def protocolsUpTo : Nat → Finset (Protocol Q)
  | 0 => {Protocol.leaf}
  | q + 1 =>
      let prev := protocolsUpTo q
      prev ∪
        Finset.univ.biUnion fun question =>
          prev.biUnion fun left =>
            prev.image fun right => Protocol.node question left right

lemma mem_protocolsUpTo_of_depth_le :
    ∀ (protocol : Protocol Q) (q : Nat), protocol.depth ≤ q → protocol ∈ protocolsUpTo q := by
  intro protocol q
  induction q with
  | zero =>
      intro h
      cases protocol with
      | leaf =>
          simp [protocolsUpTo]
      | node question left right =>
          simp [Protocol.depth] at h
  | succ q ih =>
      intro h
      cases protocol with
      | leaf =>
          change Protocol.leaf ∈
            let prev := protocolsUpTo q
            prev ∪
              Finset.univ.biUnion fun question =>
                prev.biUnion fun left =>
                  prev.image fun right => Protocol.node question left right
          dsimp
          exact Finset.mem_union.mpr (Or.inl (ih (by simp [Protocol.depth])))
      | node question left right =>
          have hMax : max left.depth right.depth ≤ q := by
            exact Nat.succ_le_succ_iff.mp (by simpa [Protocol.depth] using h)
          have hLeft : left.depth ≤ q := le_trans (le_max_left _ _) hMax
          have hRight : right.depth ≤ q := le_trans (le_max_right _ _) hMax
          have hLeftMem : left ∈ protocolsUpTo q := mem_protocolsUpTo_of_depth_le left q hLeft
          have hRightMem : right ∈ protocolsUpTo q := mem_protocolsUpTo_of_depth_le right q hRight
          simp [protocolsUpTo, hLeftMem, hRightMem]

lemma depth_le_of_mem_protocolsUpTo :
    ∀ (q : Nat) (protocol : Protocol Q), protocol ∈ protocolsUpTo q → protocol.depth ≤ q
  | 0, protocol, h => by
      have hEq : protocol = Protocol.leaf := by
        simpa [protocolsUpTo] using h
      subst hEq
      simp [Protocol.depth]
  | q + 1, protocol, h => by
      simp only [protocolsUpTo, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ,
        true_and, Finset.mem_image] at h
      rcases h with hPrev | ⟨question, left, hLeft, right, hRight, hEq⟩
      · exact le_trans (depth_le_of_mem_protocolsUpTo q protocol hPrev) (Nat.le_succ q)
      · subst hEq
        have hLeftDepth : left.depth ≤ q := depth_le_of_mem_protocolsUpTo q left hLeft
        have hRightDepth : right.depth ≤ q := depth_le_of_mem_protocolsUpTo q right hRight
        calc
          (Protocol.node question left right).depth = Nat.succ (max left.depth right.depth) := by
            simp [Protocol.depth]
          _ ≤ Nat.succ q := by
            gcongr
            exact max_le hLeftDepth hRightDepth

/-- Optimal success achievable using only questions from `Q` within depth `q`. -/
def succRestricted (family : QuestionFamily K Q) (q : Nat)
    (μ : K → NNRat) (keys : Finset K) : NNRat :=
  (protocolsUpTo q).sup fun protocol => Protocol.success family μ protocol keys

theorem success_le_succRestricted (family : QuestionFamily K Q) (μ : K → NNRat)
    (keys : Finset K) {q : Nat} {protocol : Protocol Q} (hDepth : protocol.depth ≤ q) :
    Protocol.success family μ protocol keys ≤ succRestricted family q μ keys := by
  exact Finset.le_sup
    (s := protocolsUpTo q)
    (f := fun p => Protocol.success family μ p keys)
    (b := protocol)
    (hb := mem_protocolsUpTo_of_depth_le protocol q hDepth)

/-- Global restricted optimum is upper-bounded by the unrestricted benchmark. -/
theorem succRestricted_le_succQuestions (family : QuestionFamily K Q)
    (q : Nat) (μ : K → NNRat) (keys : Finset K) :
    succRestricted family q μ keys ≤ succQuestions q μ keys := by
  rw [succRestricted]
  apply Finset.sup_le_iff.mpr
  intro protocol hProtocol
  have hDepth : protocol.depth ≤ q := depth_le_of_mem_protocolsUpTo q protocol hProtocol
  calc
    Protocol.success family μ protocol keys ≤ succQuestions protocol.depth μ keys :=
      Protocol.success_le_succQuestions family μ protocol keys
    _ ≤ succQuestions q μ keys :=
      succQuestions_mono μ keys hDepth

end OptimalRestricted

end Restricted

end SafeSlice
