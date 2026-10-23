import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheOddWeilLedgerIsFrustratedOnlyByPrimes

/-!
# Positivity is decided on the frustration terminals

**Kron reduction of a signed incidence form.**  Fix a set `T` of terminals.  A *harmonic frame*
(`HarmonicFrame`) gives for every terminal `τ ∈ T` a profile `h_τ` that is the indicator of `τ` on
`T` and harmonic off `T`: `(C h_τ)_i = 0` for `i ∉ T`.  Every profile splits as
`f = F + g`, `F = Σ_{τ∈T} f_τ h_τ`, with `g = 0` on `T`, and the energy splits without cross term:

`E(f) = R(f) + E(g)`   (`incidenceEnergy_eq_reduced_add`),

where `R_στ = (C h_τ)_σ` is the **reduced coupling** on `T` (`reduced_symm`).  Hence positivity is
the conjunction of positivity on profiles vanishing on `T` and positivity of `R`
(`nonneg_iff_interior_and_reduced`).  A frame exists whenever the form is coercive on profiles
vanishing on `T` (`exists_harmonicFrame`).

**All frustration lives on the terminals.**  If `T` contains both ends of every anti-aligned
overlap, the interior is aligned and its positivity is local payment (mechanism 4):
`E ≥ 0 ⟺ (interior locally payable) ∧ R ≥ 0` (`nonneg_iff_interior_payable_and_reduced`).

**One frustrated overlap.**  For `T = {a, b}` with `c_ab = t`, `R` is the binary form with
effective budgets `α = (C h_a)_a`, `γ = (C h_b)_b` and off-diagonal `t − β`, where
`β = −Σ_{i∉T} c_ai h_b(i)` is the **effective conductance** of the interior between `a` and `b`
(`reduced_offDiag_eq`): the form is nonnegative iff the interior is and
`α, γ ≥ 0`, `(t − β)² ≤ αγ` (`nonneg_iff_two_terminal`).  The overlap is paid by the effective
conductance (nonlocal) plus the geometric mean of the effective budgets (local).  A frustrated
cycle (mechanism 12) is the case of a single path; on networks with parallel paths a single
canonical path overpays and the effective conductance is the exact price.

**Arithmetic instance.**  In the odd Weil ledger every anti-aligned overlap joins two positions
whose sum is a prime-power logarithm (mechanism 15), so its terminals are prime-sum endpoints
(`oddWeilLedger_terminal_primeSum`).
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Harmonic frames and the reduced coupling -/

/-- A **harmonic frame** on the terminals `T`: profiles `h_τ` equal to the indicator of `τ` on `T`
and harmonic off `T`. -/
structure HarmonicFrame (c : ι → ι → ℝ) (T : Finset ι) where
  /-- The harmonic extension `h_τ` of the terminal `τ`. -/
  h : ι → ι → ℝ
  boundary : ∀ τ ∈ T, ∀ σ ∈ T, h τ σ = if σ = τ then 1 else 0
  harmonic : ∀ τ ∈ T, ∀ i ∉ T, couplingAction c (h τ) i = 0

variable {c : ι → ι → ℝ} {T : Finset ι}

/-- The reduced coupling `R_στ = (C h_τ)_σ` on `T × T`, zero elsewhere. -/
def HarmonicFrame.reduced (H : HarmonicFrame c T) : ι → ι → ℝ :=
  fun σ τ => if σ ∈ T ∧ τ ∈ T then couplingAction c (H.h τ) σ else 0

/-- The harmonic extension `F = Σ_{τ∈T} f_τ h_τ` of the terminal values of `f`. -/
def HarmonicFrame.extend (H : HarmonicFrame c T) (f : ι → ℝ) : ι → ℝ :=
  fun i => ∑ τ ∈ T, f τ * H.h τ i

theorem HarmonicFrame.extend_of_mem (H : HarmonicFrame c T) (f : ι → ℝ) {σ : ι} (hσ : σ ∈ T) :
    H.extend f σ = f σ := by
  unfold HarmonicFrame.extend
  rw [sum_congr rfl fun τ hτ => by rw [H.boundary τ hτ σ hσ]]
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq T σ]
  simp [hσ]

theorem HarmonicFrame.action_extend (H : HarmonicFrame c T) (f : ι → ℝ) (i : ι) :
    couplingAction c (H.extend f) i = ∑ τ ∈ T, f τ * couplingAction c (H.h τ) i := by
  unfold couplingAction HarmonicFrame.extend
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun τ _ => sum_congr rfl fun j _ => by ring

theorem HarmonicFrame.action_extend_of_not_mem (H : HarmonicFrame c T) (f : ι → ℝ) {i : ι}
    (hi : i ∉ T) : couplingAction c (H.extend f) i = 0 := by
  rw [H.action_extend]
  exact sum_eq_zero fun τ hτ => by rw [H.harmonic τ hτ i hi, mul_zero]

omit [DecidableEq ι] in
/-- A sum over all points of a profile times an action vanishing off `T` is a sum over `T`. -/
theorem sum_mul_eq_sum_terminals [DecidableEq ι] (T : Finset ι) (u v : ι → ℝ)
    (hv : ∀ i ∉ T, v i = 0) : ∑ i, u i * v i = ∑ i ∈ T, u i * v i := by
  rw [← sum_subset (subset_univ T) fun i _ hi => by rw [hv i hi, mul_zero]]

/-- **The reduced energy**: `E(F) = R(f)`. -/
theorem HarmonicFrame.energy_extend (H : HarmonicFrame c T) (f : ι → ℝ) :
    incidenceEnergy c (H.extend f) = incidenceEnergy H.reduced f := by
  rw [incidenceEnergy_eq_sum_mul_couplingAction,
    sum_mul_eq_sum_terminals T _ _ fun i hi => H.action_extend_of_not_mem f hi]
  unfold incidenceEnergy HarmonicFrame.reduced
  have hrow : ∀ σ, ∑ τ, (if σ ∈ T ∧ τ ∈ T then couplingAction c (H.h τ) σ else 0) * f σ * f τ =
      if σ ∈ T then ∑ τ ∈ T, couplingAction c (H.h τ) σ * f σ * f τ else 0 := by
    intro σ
    by_cases hσ : σ ∈ T
    · rw [if_pos hσ, ← sum_subset (subset_univ T) fun τ _ hτ => by simp [hτ]]
      exact sum_congr rfl fun τ hτ => by simp [hσ, hτ]
    · rw [if_neg hσ]; exact sum_eq_zero fun τ _ => by simp [hσ]
  rw [sum_congr rfl fun σ _ => hrow σ, ← sum_subset (subset_univ T) fun σ _ hσ => by simp [hσ]]
  refine sum_congr rfl fun σ hσ => ?_
  rw [if_pos hσ, H.extend_of_mem f hσ, H.action_extend, mul_sum]
  exact sum_congr rfl fun τ _ => by ring

/-- **Splitting without cross term**: `E(f) = R(f) + E(f − F)`, and `f − F` vanishes on `T`. -/
theorem incidenceEnergy_eq_reduced_add (hc : IsSymmetricCoupling c) (H : HarmonicFrame c T)
    (f : ι → ℝ) :
    incidenceEnergy c f =
      incidenceEnergy H.reduced f + incidenceEnergy c (fun i => f i - H.extend f i) := by
  have hsub := incidenceEnergy_sub hc f (H.extend f)
  have hcross : ∑ i, f i * couplingAction c (H.extend f) i = incidenceEnergy c (H.extend f) := by
    rw [incidenceEnergy_eq_sum_mul_couplingAction,
      sum_mul_eq_sum_terminals T _ _ fun i hi => H.action_extend_of_not_mem f hi,
      sum_mul_eq_sum_terminals T _ _ fun i hi => H.action_extend_of_not_mem f hi]
    exact sum_congr rfl fun σ hσ => by rw [H.extend_of_mem f hσ]
  rw [hcross, H.energy_extend] at hsub
  linarith

theorem HarmonicFrame.sub_extend_of_mem (H : HarmonicFrame c T) (f : ι → ℝ) {σ : ι}
    (hσ : σ ∈ T) : f σ - H.extend f σ = 0 := by
  rw [H.extend_of_mem f hσ, sub_self]

/-- **The reduced coupling is symmetric**: `(C h_τ)_σ = (C h_σ)_τ`. -/
theorem HarmonicFrame.reduced_symm (hc : IsSymmetricCoupling c) (H : HarmonicFrame c T) :
    IsSymmetricCoupling H.reduced := by
  intro σ τ
  unfold HarmonicFrame.reduced
  by_cases h : σ ∈ T ∧ τ ∈ T
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    -- both sides are the pairing `Σ_{i,j} h_σ(i) c_ij h_τ(j)`
    have pair : ∀ {σ τ : ι}, σ ∈ T → τ ∈ T →
        ∑ i, H.h σ i * couplingAction c (H.h τ) i = couplingAction c (H.h τ) σ := by
      intro σ τ hσ hτ
      rw [sum_mul_eq_sum_terminals T _ _ fun i hi => H.harmonic τ hτ i hi]
      rw [sum_congr rfl fun i hi => by rw [H.boundary σ hσ i hi]]
      simp only [ite_mul, one_mul, zero_mul]
      rw [sum_ite_eq' T σ]
      simp [hσ]
    rw [← pair h.1 h.2, ← pair h.2 h.1]
    unfold couplingAction
    simp_rw [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hc j i]; ring
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]

/-! ### Positivity on the terminals -/

/-- **Positivity is decided on the terminals**: `E ≥ 0` iff `E ≥ 0` on profiles vanishing on `T`
and the reduced coupling is nonnegative. -/
theorem nonneg_iff_interior_and_reduced (hc : IsSymmetricCoupling c) (H : HarmonicFrame c T) :
    (∀ f, 0 ≤ incidenceEnergy c f) ↔
      (∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → 0 ≤ incidenceEnergy c g) ∧
        ∀ f, 0 ≤ incidenceEnergy H.reduced f := by
  constructor
  · intro h
    exact ⟨fun g _ => h g, fun f => by rw [← H.energy_extend]; exact h _⟩
  · rintro ⟨hI, hR⟩ f
    rw [incidenceEnergy_eq_reduced_add hc H f]
    exact add_nonneg (hR f) (hI _ fun τ hτ => H.sub_extend_of_mem f hτ)

/-- **Harmonic frames exist** when the form is coercive on profiles vanishing on `T`. -/
theorem exists_harmonicFrame (c : ι → ι → ℝ) (T : Finset ι) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → δ * ∑ i, g i ^ 2 ≤ incidenceEnergy c g) :
    Nonempty (HarmonicFrame c T) := by
  -- `M h = h` on `T`, `M h = C h` off `T`; injective by coercivity, hence surjective
  let M : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun v i => if i ∈ T then v i else couplingAction c v i
      map_add' := fun v w => by
        funext i
        simp only [Pi.add_apply]
        split_ifs
        · rfl
        · unfold couplingAction; rw [← sum_add_distrib]
          exact sum_congr rfl fun j _ => by ring
      map_smul' := fun r v => by
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        split_ifs
        · rfl
        · unfold couplingAction; rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring }
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hvT : ∀ τ ∈ T, v τ = 0 := fun τ hτ => by
      have := congrFun hv τ
      simpa [M, hτ] using this
    have hvC : ∀ i ∉ T, couplingAction c v i = 0 := fun i hi => by
      have := congrFun hv i
      simpa [M, hi] using this
    have hE : incidenceEnergy c v = 0 := by
      rw [incidenceEnergy_eq_sum_mul_couplingAction]
      refine sum_eq_zero fun i _ => ?_
      by_cases hi : i ∈ T
      · rw [hvT i hi, zero_mul]
      · rw [hvC i hi, mul_zero]
    have h1 := hcoer v hvT
    rw [hE] at h1
    have hsq : ∑ i, v i ^ 2 = 0 := by
      have h0 : 0 ≤ ∑ i, v i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (v i)).mp hsq i (mem_univ i)
    simpa using this
  have hsurj : Function.Surjective M := LinearMap.injective_iff_surjective.mp hinj
  choose h hh using fun τ : ι => hsurj (fun i => if i ∈ T then (if i = τ then 1 else 0) else 0)
  refine ⟨⟨h, fun τ _ σ hσ => ?_, fun τ _ i hi => ?_⟩⟩
  · have := congrFun (hh τ) σ
    simpa [M, hσ] using this
  · have := congrFun (hh τ) i
    simpa [M, hi] using this

/-! ### All frustration lives on the terminals -/

/-- The interior coupling: `c` on pairs off `T`, unit budget on `T`, no other overlap. -/
def interiorCoupling (c : ι → ι → ℝ) (T : Finset ι) : ι → ι → ℝ := fun i j =>
  if i ∉ T ∧ j ∉ T then c i j else if i = j then 1 else 0

omit [DecidableEq ι] in
theorem interiorCoupling_symm [DecidableEq ι] (hc : IsSymmetricCoupling c) (T : Finset ι) :
    IsSymmetricCoupling (interiorCoupling c T) := by
  intro i j
  unfold interiorCoupling
  by_cases h : i ∉ T ∧ j ∉ T
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hc i j]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]

/-- The interior coupling sees a profile through its interior part plus the unit terminal mass. -/
theorem incidenceEnergy_interiorCoupling (T : Finset ι) (f : ι → ℝ) :
    incidenceEnergy (interiorCoupling c T) f =
      incidenceEnergy c (fun i => if i ∈ T then 0 else f i) + ∑ i ∈ T, f i ^ 2 := by
  unfold incidenceEnergy interiorCoupling
  have e : ∀ i j, (if i ∉ T ∧ j ∉ T then c i j else if i = j then (1 : ℝ) else 0) * f i * f j =
      c i j * (if i ∈ T then 0 else f i) * (if j ∈ T then 0 else f j) +
        (if i ∈ T ∧ i = j then f i ^ 2 else 0) := by
    intro i j
    by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;> by_cases hij : i = j <;>
      simp_all [sq] <;> subst_vars <;> simp_all
  simp_rw [e, sum_add_distrib]
  congr 1
  rw [← sum_subset (subset_univ T) fun i _ hi => by simp [hi]]
  refine sum_congr rfl fun i hi => ?_
  rw [sum_ite_eq]
  simp [hi]

/-- **All frustration lives on the terminals.**  If every anti-aligned overlap has both ends in
`T`, then `E ≥ 0` iff the aligned interior is locally payable and the reduced coupling on `T` is
nonnegative. -/
theorem nonneg_iff_interior_payable_and_reduced (hc : IsSymmetricCoupling c)
    (hT : ∀ i j, i ≠ j → 0 < c i j → i ∈ T ∧ j ∈ T) (H : HarmonicFrame c T) :
    (∀ f, 0 ≤ incidenceEnergy c f) ↔
      LocallyPayable (interiorCoupling c T) ∧ ∀ f, 0 ≤ incidenceEnergy H.reduced f := by
  have hsymI := interiorCoupling_symm hc T
  have halign : HasNonpositiveOverlaps (interiorCoupling c T) := by
    intro i j hij
    unfold interiorCoupling
    by_cases h : i ∉ T ∧ j ∉ T
    · rw [if_pos h]
      by_contra hpos
      exact h.1 (hT i j hij (lt_of_not_ge hpos)).1
    · rw [if_neg h, if_neg hij]
  have hbal : IsBalanced (interiorCoupling c T) := isBalanced_of_aligned halign
  have hint : (∀ g : ι → ℝ, (∀ τ ∈ T, g τ = 0) → 0 ≤ incidenceEnergy c g) ↔
      ∀ f, 0 ≤ incidenceEnergy (interiorCoupling c T) f := by
    constructor
    · intro h f
      rw [incidenceEnergy_interiorCoupling]
      exact add_nonneg (h _ fun τ hτ => by simp [hτ]) (sum_nonneg fun i _ => sq_nonneg _)
    · intro h g hg
      have := h g
      rw [incidenceEnergy_interiorCoupling] at this
      have e : (fun i => if i ∈ T then 0 else g i) = g := by
        funext i; split_ifs with hi
        · exact (hg i hi).symm
        · rfl
      have e2 : ∑ i ∈ T, g i ^ 2 = 0 := sum_eq_zero fun i hi => by rw [hg i hi]; ring
      rw [e, e2, add_zero] at this
      exact this
  rw [nonneg_iff_interior_and_reduced hc H, hint, nonneg_iff_locallyPayable_of_isBalanced hsymI hbal]

/-! ### One frustrated overlap -/

/-- A binary form `α x² + 2κ x y + γ y²` is nonnegative iff `α, γ ≥ 0` and `κ² ≤ αγ`. -/
theorem binaryForm_nonneg_iff {α γ κ : ℝ} :
    (∀ x y : ℝ, 0 ≤ α * x ^ 2 + 2 * κ * x * y + γ * y ^ 2) ↔ 0 ≤ α ∧ 0 ≤ γ ∧ κ ^ 2 ≤ α * γ := by
  constructor
  · intro h
    have hα : 0 ≤ α := by simpa using h 1 0
    have hγ : 0 ≤ γ := by simpa using h 0 1
    refine ⟨hα, hγ, ?_⟩
    have h1 := h γ (-κ)
    have h2 := h (-κ) α
    nlinarith [sq_nonneg κ, mul_nonneg hα hγ]
  · rintro ⟨hα, hγ, hκ⟩ x y
    exact binaryForm_nonneg hα hγ hκ x y

/-- On two terminals the reduced energy is the binary form of the effective budgets and the
effective off-diagonal. -/
theorem HarmonicFrame.reduced_energy_pair {a b : ι} (hab : a ≠ b)
    (H : HarmonicFrame c {a, b}) (hc : IsSymmetricCoupling c) (f : ι → ℝ) :
    incidenceEnergy H.reduced f =
      H.reduced a a * f a ^ 2 + 2 * H.reduced a b * f a * f b + H.reduced b b * f b ^ 2 := by
  have hsym := H.reduced_symm hc
  have hzero : ∀ σ τ, ¬ (σ ∈ ({a, b} : Finset ι) ∧ τ ∈ ({a, b} : Finset ι)) →
      H.reduced σ τ = 0 := fun σ τ h => by simp only [HarmonicFrame.reduced, if_neg h]
  unfold incidenceEnergy
  have hrow : ∀ σ, ∑ τ, H.reduced σ τ * f σ * f τ =
      H.reduced σ a * f σ * f a + H.reduced σ b * f σ * f b := by
    intro σ
    rw [← sum_subset (subset_univ {a, b}) fun τ _ hτ => by
      rw [hzero σ τ fun h => hτ h.2]; ring]
    rw [sum_pair hab]
  rw [sum_congr rfl fun σ _ => hrow σ,
    ← sum_subset (subset_univ {a, b}) fun σ _ hσ => by
      rw [hzero σ a fun h => hσ h.1, hzero σ b fun h => hσ h.1]; ring,
    sum_pair hab, hsym b a]
  ring

/-- **The effective conductance**: with `c_ab = t`, the reduced off-diagonal is `t − β`,
`β = −Σ_{i ∉ {a,b}} c_ai h_b(i)`. -/
theorem HarmonicFrame.reduced_offDiag_eq {a b : ι} (hab : a ≠ b) (H : HarmonicFrame c {a, b}) :
    H.reduced a b =
      c a b - (-∑ i ∈ (univ.erase a).erase b, c a i * H.h b i) := by
  have ha : a ∈ ({a, b} : Finset ι) := mem_insert_self a {b}
  have hb : b ∈ ({a, b} : Finset ι) := mem_insert_of_mem (mem_singleton_self b)
  simp only [HarmonicFrame.reduced, if_pos (And.intro ha hb), couplingAction]
  rw [← add_sum_erase _ _ (mem_univ a), ← add_sum_erase _ _ (mem_erase.mpr ⟨Ne.symm hab, mem_univ b⟩),
    H.boundary b hb a ha, H.boundary b hb b hb]
  simp [hab]

/-- **The price of one frustrated overlap.**  For a harmonic frame on `{a, b}`, `E ≥ 0` iff `E ≥ 0`
on profiles vanishing at `a, b`, the effective budgets `α = R_aa`, `γ = R_bb` are nonnegative, and
`(t − β)² ≤ αγ` with `t = c_ab` and `β` the effective conductance of the interior. -/
theorem nonneg_iff_two_terminal (hc : IsSymmetricCoupling c) {a b : ι} (hab : a ≠ b)
    (H : HarmonicFrame c {a, b}) :
    (∀ f, 0 ≤ incidenceEnergy c f) ↔
      (∀ g : ι → ℝ, g a = 0 → g b = 0 → 0 ≤ incidenceEnergy c g) ∧
        0 ≤ H.reduced a a ∧ 0 ≤ H.reduced b b ∧
          (c a b - (-∑ i ∈ (univ.erase a).erase b, c a i * H.h b i)) ^ 2 ≤
            H.reduced a a * H.reduced b b := by
  rw [nonneg_iff_interior_and_reduced hc H, ← H.reduced_offDiag_eq hab]
  have hR : (∀ f, 0 ≤ incidenceEnergy H.reduced f) ↔
      ∀ x y : ℝ, 0 ≤ H.reduced a a * x ^ 2 + 2 * H.reduced a b * x * y + H.reduced b b * y ^ 2 := by
    constructor
    · intro h x y
      have := h fun i => if i = a then x else if i = b then y else 0
      rw [H.reduced_energy_pair hab hc] at this
      simpa [hab, Ne.symm hab] using this
    · intro h f
      rw [H.reduced_energy_pair hab hc]
      exact h _ _
  rw [hR, binaryForm_nonneg_iff]
  constructor
  · rintro ⟨hI, h⟩
    exact ⟨fun g ga gb => hI g fun τ hτ => by
      rcases mem_insert.mp hτ with rfl | hτ
      · exact ga
      · rw [mem_singleton.mp hτ]; exact gb, h⟩
  · rintro ⟨hI, h⟩
    exact ⟨fun g hg => hI g (hg a (mem_insert_self a {b}))
      (hg b (mem_insert_of_mem (mem_singleton_self b))), h⟩

/-! ### The odd Weil ledger -/

/-- **The terminals of the odd Weil ledger are prime-sum endpoints**: every point carrying an
anti-aligned overlap of the sampled ledger with kernel `α K + β · prime` (`α, β ≥ 0`) has a
partner whose position sum is the logarithm of a prime power.  So the Kron reduction of the odd
Weil ledger lives on prime-sum endpoints and its interior is aligned. -/
theorem oddWeilLedger_terminal_primeSum {p : ι → ℝ} (hp : ∀ x, 0 < p x)
    (hinj : Function.Injective p) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) {b : ι → ℝ} {x y : ι}
    (hxy : x ≠ y) (h : 0 < oddFold p (weilLedgerKernel α β) b x y) :
    (∃ n : ℕ, Real.exp (p x + p y) = n ∧ 0 < ArithmeticFunction.vonMangoldt n) ∧
      (∃ n : ℕ, Real.exp (p y + p x) = n ∧ 0 < ArithmeticFunction.vonMangoldt n) := by
  obtain ⟨n, hn, hΛ⟩ := oddFold_pos_imp_primeSum hp hinj hα hβ hxy h
  exact ⟨⟨n, hn, hΛ⟩, ⟨n, by rw [add_comm]; exact hn, hΛ⟩⟩

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
