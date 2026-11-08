import GaloisForLFunctions.InfiniteRankWeilTheory.WellFoundedTowersSelfImprove

/-!
# The exceptional coordinate

At infinite rank there is no crude regime in the size coordinate. What survives of "crude" is the
**exceptional coordinate**: the number of modes beyond each depth. This file states the three steps
of the curve proof in that coordinate for an arbitrary configuration `ρ : ι → ℂ` (modes with
multiplicity) and proves the dictionary with towers.

* `rightRH_iff_zerosApproachLine_and_asymptoticAbscissaLaw`: for every configuration, "no mode right
  of `½`" is ZAL (finitely many modes beyond each positive depth) plus AAL (a finite exceptional set
  beyond any depth is empty). The split holds for every family, with no arithmetic input.
* `not_asymptoticAbscissaLaw_iff_hasIsolatedTop`: AAL fails exactly when the configuration has an
  **isolated top**: a finite nonempty layer on a line `Re = Θ > ½` with every other mode left of some
  `Θ₂ < Θ`. So a failure of AAL is a finite-rank Weil datum riding on an infinite-rank remainder.
* `asymptoticAbscissaLaw_iff_eventualToGlobal`: for locally finite configurations AAL is the
  eventual-to-global law at every abscissa `σ ≥ ½`.
* `wellFoundedAbove_frobTower_iff`: in the tower `z_i = e^{ℓ(ρ_i−½)}`, `ℓ > 0`, ZAL is
  well-foundedness of the outer part above `1`; `frobTower_isolatedTop` turns an isolated top into the
  window data of `TheExceptionalRankDecidesTheWindow`.
* `asymptoticAbscissaLaw_of_vertical_period`: a configuration invariant under a vertical translation
  satisfies AAL (function fields: the head is periodic, so AAL is automatic).
* `asymptoticAbscissaLaw_shift_iff`: symmetric shifts `ρ ± a` preserve AAL for every reflection-closed
  configuration of infinite rank. A proof of AAL may use the functional equation only as an
  involution, never the position of the line.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.InfiniteRankWeilTheory

variable {ι : Type*}

/-- **ZAL**: finitely many modes beyond every positive depth. -/
def ZerosApproachLine (ρ : ι → ℂ) : Prop :=
  ∀ h : ℝ, 0 < h → {i | 1 / 2 + h < (ρ i).re}.Finite

/-- **AAL**: a finite exceptional set beyond a depth `h ≥ 0` is empty. -/
def AsymptoticAbscissaLaw (ρ : ι → ℂ) : Prop :=
  ∀ h : ℝ, 0 ≤ h → {i | 1 / 2 + h < (ρ i).re}.Finite → ∀ i, (ρ i).re ≤ 1 / 2 + h

/-- No mode right of the critical line. -/
def RightRH (ρ : ι → ℂ) : Prop := ∀ i, (ρ i).re ≤ 1 / 2

/-- **RH is ZAL plus AAL**, for every configuration. -/
theorem rightRH_iff_zerosApproachLine_and_asymptoticAbscissaLaw (ρ : ι → ℂ) :
    RightRH ρ ↔ ZerosApproachLine ρ ∧ AsymptoticAbscissaLaw ρ := by
  constructor
  · intro h
    refine ⟨fun δ hδ => ?_, fun δ hδ _ i => (h i).trans (by linarith)⟩
    convert Set.finite_empty
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact (h i).trans (by linarith)
  · rintro ⟨hZ, hA⟩ i
    by_contra hi
    push Not at hi
    have hδ : 0 < ((ρ i).re - 1 / 2) / 2 := by linarith
    have := hA _ hδ.le (hZ _ hδ) i
    linarith

/-- An **isolated top**: a finite nonempty layer on `Re = Θ > ½`, every other mode left of `Θ₂ < Θ`. -/
def HasIsolatedTop (ρ : ι → ℂ) : Prop :=
  ∃ (F : Finset ι) (Θ Θ₂ : ℝ), F.Nonempty ∧ 1 / 2 < Θ ∧ Θ₂ < Θ ∧
    (∀ i ∈ F, (ρ i).re = Θ) ∧ ∀ i ∉ F, (ρ i).re ≤ Θ₂

/-- **AAL fails exactly at an isolated top.** -/
theorem not_asymptoticAbscissaLaw_iff_hasIsolatedTop (ρ : ι → ℂ) :
    ¬ AsymptoticAbscissaLaw ρ ↔ HasIsolatedTop ρ := by
  classical
  constructor
  · intro hnot
    simp only [AsymptoticAbscissaLaw, not_forall, not_le] at hnot
    obtain ⟨h, hh, hfin, i₀, hi₀⟩ := hnot
    set E := hfin.toFinset with hE
    have hmemE : ∀ i, i ∈ E ↔ 1 / 2 + h < (ρ i).re := fun i => by simp [hE]
    obtain ⟨im, himE, himax⟩ :=
      E.exists_max_image (fun i => (ρ i).re) ⟨i₀, (hmemE i₀).2 hi₀⟩
    set Θ := (ρ im).re
    set F := E.filter (fun i => (ρ i).re = Θ)
    set L := E.filter (fun i => (ρ i).re ≠ Θ)
    obtain ⟨Θ₂, hΘ₂, hhΘ₂, hL⟩ : ∃ Θ₂ : ℝ, Θ₂ < Θ ∧ 1 / 2 + h ≤ Θ₂ ∧ ∀ i ∈ L, (ρ i).re ≤ Θ₂ := by
      by_cases hLn : L.Nonempty
      · obtain ⟨jl, hjl, hjlmax⟩ := L.exists_max_image (fun i => (ρ i).re) hLn
        obtain ⟨hjlE, hjlne⟩ := Finset.mem_filter.1 hjl
        refine ⟨max (1 / 2 + h) (ρ jl).re, max_lt ((hmemE im).1 himE)
          (lt_of_le_of_ne (himax jl hjlE) hjlne), le_max_left _ _,
          fun i hi => (hjlmax i hi).trans (le_max_right _ _)⟩
      · exact ⟨1 / 2 + h, (hmemE im).1 himE, le_rfl, fun i hi => absurd ⟨i, hi⟩ hLn⟩
    refine ⟨F, Θ, Θ₂, ⟨im, Finset.mem_filter.2 ⟨himE, rfl⟩⟩, by linarith [(hmemE im).1 himE],
      hΘ₂, fun i hi => (Finset.mem_filter.1 hi).2, fun i hi => ?_⟩
    by_cases hiE : i ∈ E
    · have hne : (ρ i).re ≠ Θ := fun heq => hi (Finset.mem_filter.2 ⟨hiE, heq⟩)
      exact hL i (Finset.mem_filter.2 ⟨hiE, hne⟩)
    · have : ¬ 1 / 2 + h < (ρ i).re := fun h' => hiE ((hmemE i).2 h')
      linarith
  · rintro ⟨F, Θ, Θ₂, ⟨i₀, hi₀⟩, hΘ, hΘ₂, hF, hrest⟩ hA
    set h := max Θ₂ (1 / 2) - 1 / 2
    have hh : 0 ≤ h := by simp only [h]; linarith [le_max_right Θ₂ (1 / 2)]
    have hfin : {i | 1 / 2 + h < (ρ i).re}.Finite := by
      refine (F.finite_toSet).subset fun i hi => ?_
      by_contra hiF
      have := hrest i hiF
      simp only [Set.mem_setOf_eq, h] at hi
      linarith [le_max_left Θ₂ (1 / 2)]
    have := hA h hh hfin i₀
    rw [hF i₀ hi₀] at this
    simp only [h] at this
    have : max Θ₂ (1 / 2) < Θ := max_lt hΘ₂ hΘ
    linarith

/-- A configuration is **locally finite** if only finitely many modes lie below every height. -/
def LocallyFinite (ρ : ι → ℂ) : Prop := ∀ T : ℝ, {i | |(ρ i).im| < T}.Finite

/-- The **eventual-to-global law** at every abscissa `σ ≥ ½`. -/
def EventualToGlobal (ρ : ι → ℂ) : Prop :=
  ∀ σ : ℝ, 1 / 2 ≤ σ → (∃ T : ℝ, ∀ i, T ≤ |(ρ i).im| → (ρ i).re ≤ σ) → ∀ i, (ρ i).re ≤ σ

/-- **AAL is the eventual-to-global law** for locally finite configurations. -/
theorem asymptoticAbscissaLaw_iff_eventualToGlobal {ρ : ι → ℂ} (hlf : LocallyFinite ρ) :
    AsymptoticAbscissaLaw ρ ↔ EventualToGlobal ρ := by
  classical
  constructor
  · intro hA σ hσ ⟨T, hT⟩
    have hfin : {i | 1 / 2 + (σ - 1 / 2) < (ρ i).re}.Finite := by
      refine (hlf T).subset fun i hi => ?_
      by_contra hlt
      simp only [Set.mem_setOf_eq, not_lt] at hi hlt
      linarith [hT i hlt]
    intro i
    have := hA (σ - 1 / 2) (by linarith) hfin i
    linarith
  · intro hE h hh hfin i
    obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ i, T ≤ |(ρ i).im| → (ρ i).re ≤ 1 / 2 + h := by
      obtain ⟨M, hM⟩ := (hfin.image fun i => |(ρ i).im|).bddAbove
      refine ⟨M + 1, fun i hi => ?_⟩
      by_contra hlt
      push Not at hlt
      have := hM ⟨i, hlt, rfl⟩
      linarith
    exact hE (1 / 2 + h) (by linarith) ⟨T, hT⟩ i

/-! ### The tower dictionary -/

/-- The tower of a configuration at base `ℓ`: `z_i = e^{ℓ(ρ_i − ½)}`. -/
def frobTower (ℓ : ℝ) (ρ : ι → ℂ) : ι → ℂ := fun i => Complex.exp (ℓ * (ρ i - 1 / 2))

theorem norm_frobTower (ℓ : ℝ) (ρ : ι → ℂ) (i : ι) :
    ‖frobTower ℓ ρ i‖ = Real.exp (ℓ * ((ρ i).re - 1 / 2)) := by
  rw [frobTower, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- `frobTower ℓ ρ i ^ ν = e^{νℓ(ρ_i − ½)}`. -/
theorem frobTower_pow (ℓ : ℝ) (ρ : ι → ℂ) (i : ι) (ν : ℕ) :
    frobTower ℓ ρ i ^ ν = Complex.exp ((ν * ℓ : ℝ) * (ρ i - 1 / 2)) := by
  rw [frobTower, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **ZAL is well-foundedness of the tower.** At every base `ℓ > 0`. -/
theorem wellFoundedAbove_frobTower_iff {ℓ : ℝ} (hℓ : 0 < ℓ) (ρ : ι → ℂ) :
    WellFoundedAbove (frobTower ℓ ρ) 1 ↔ ZerosApproachLine ρ := by
  have key : ∀ h : ℝ,
      {i | Real.exp (ℓ * h) < ‖frobTower ℓ ρ i‖} = {i | 1 / 2 + h < (ρ i).re} := by
    intro h
    ext i
    simp only [Set.mem_setOf_eq, norm_frobTower, Real.exp_lt_exp]
    constructor
    · intro hlt
      have := lt_of_mul_lt_mul_left hlt hℓ.le
      linarith
    · intro hlt
      exact mul_lt_mul_of_pos_left (by linarith) hℓ
  constructor
  · intro hwf h hh
    rw [← key]
    refine hwf _ ?_
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (mul_pos hℓ hh)
  · intro hZ r hr
    have hr0 : 0 < r := by linarith
    have := hZ _ (div_pos (Real.log_pos hr) hℓ)
    rw [← key, mul_div_cancel₀ _ hℓ.ne', Real.exp_log hr0] at this
    exact this

/-- An isolated top gives the window data of a tower: a finite top of modulus `R = e^{ℓ(Θ−½)}` over
a remainder of modulus `≤ r = e^{ℓ(Θ₂−½)} < R`. -/
theorem frobTower_isolatedTop {ℓ : ℝ} (hℓ : 0 < ℓ) {ρ : ι → ℂ} {F : Finset ι} {Θ Θ₂ : ℝ}
    (hΘ₂ : Θ₂ < Θ) (hF : ∀ i ∈ F, (ρ i).re = Θ) (hrest : ∀ i ∉ F, (ρ i).re ≤ Θ₂) :
    (∀ i ∈ F, ‖frobTower ℓ ρ i‖ = Real.exp (ℓ * (Θ - 1 / 2))) ∧
      (∀ i ∉ F, ‖frobTower ℓ ρ i‖ ≤ Real.exp (ℓ * (Θ₂ - 1 / 2))) ∧
      Real.exp (ℓ * (Θ₂ - 1 / 2)) < Real.exp (ℓ * (Θ - 1 / 2)) := by
  refine ⟨fun i hi => by rw [norm_frobTower, hF i hi], fun i hi => ?_, ?_⟩
  · rw [norm_frobTower]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hrest i hi]) hℓ.le)
  · exact Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left (by linarith) hℓ)

/-! ### Periodic configurations and symmetric shifts -/

/-- **Function fields.** A configuration invariant under a vertical translation `ρ ↦ ρ + iτ`,
`τ ≠ 0`, satisfies AAL: every nonempty exceptional set is infinite. -/
theorem asymptoticAbscissaLaw_of_vertical_period {ρ : ι → ℂ} (σ : Equiv.Perm ι) {τ : ℝ}
    (hτ : τ ≠ 0) (hσ : ∀ i, ρ (σ i) = ρ i + τ * I) : AsymptoticAbscissaLaw ρ := by
  intro h _ hfin i
  by_contra hi
  push Not at hi
  have hre : ∀ n : ℕ, (ρ ((σ ^ n) i)).re = (ρ i).re ∧ (ρ ((σ ^ n) i)).im = (ρ i).im + n * τ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, hσ]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, ih.1, ih.2]
      push_cast
      constructor <;> ring
  have hinj : Function.Injective fun n : ℕ => (σ ^ n) i := by
    intro m n hmn
    have h1 := (hre m).2
    have h2 := (hre n).2
    simp only at hmn
    rw [hmn] at h1
    have : (m : ℝ) * τ = n * τ := by linarith
    exact_mod_cast mul_right_cancel₀ hτ this
  exact Set.infinite_of_injective_forall_mem hinj (fun n => by
    simp only [Set.mem_setOf_eq, (hre n).1]; exact hi) hfin

/-- The symmetric shift `ρ ± a` of a configuration. -/
def symmetricShift (ρ : ι → ℂ) (a : ℝ) : ι ⊕ ι → ℂ := Sum.elim (fun i => ρ i + a) (fun i => ρ i - a)

/-- In a reflection-closed configuration of infinite rank, infinitely many modes lie on or right of
the critical line. -/
theorem infinite_re_ge_half {ρ : ι → ℂ} [Infinite ι] (fe : Equiv.Perm ι)
    (hfe : ∀ i, ρ (fe i) = 1 - ρ i) : {i | 1 / 2 ≤ (ρ i).re}.Infinite := by
  intro hfin
  have hcover : (Set.univ : Set ι) ⊆ {i | 1 / 2 ≤ (ρ i).re} ∪ fe ⁻¹' {i | 1 / 2 ≤ (ρ i).re} := by
    intro i _
    by_cases hi : 1 / 2 ≤ (ρ i).re
    · exact Or.inl hi
    · right
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hfe, Complex.sub_re, Complex.one_re]
      linarith
  exact Set.infinite_univ ((hfin.union (hfin.preimage fe.injective.injOn)).subset hcover)

/-- **Symmetric shifts preserve AAL** for reflection-closed configurations of infinite rank. -/
theorem asymptoticAbscissaLaw_shift_iff {ρ : ι → ℂ} [Infinite ι] (fe : Equiv.Perm ι)
    (hfe : ∀ i, ρ (fe i) = 1 - ρ i) {a : ℝ} (ha : 0 ≤ a) :
    AsymptoticAbscissaLaw (symmetricShift ρ a) ↔ AsymptoticAbscissaLaw ρ := by
  have hre_l : ∀ i, (symmetricShift ρ a (Sum.inl i)).re = (ρ i).re + a := fun i => by
    simp [symmetricShift]
  have hre_r : ∀ i, (symmetricShift ρ a (Sum.inr i)).re = (ρ i).re - a := fun i => by
    simp [symmetricShift]
  constructor
  · intro hS h hh hfin i
    have hfin' : {j | 1 / 2 + (h + a) < (symmetricShift ρ a j).re}.Finite := by
      refine ((hfin.image Sum.inl).union (hfin.image Sum.inr)).subset ?_
      rintro (j | j) hj
      · left
        refine ⟨j, ?_, rfl⟩
        simp only [Set.mem_setOf_eq, hre_l] at hj ⊢
        linarith
      · right
        refine ⟨j, ?_, rfl⟩
        simp only [Set.mem_setOf_eq, hre_r] at hj ⊢
        linarith
    have := hS (h + a) (by linarith) hfin' (Sum.inl i)
    rw [hre_l] at this
    linarith
  · intro hA h hh hfin j
    have hfinl : {i | 1 / 2 + h - a < (ρ i).re}.Finite := by
      refine (hfin.preimage Sum.inl_injective.injOn).subset fun i hi => ?_
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hre_l] at hi ⊢
      linarith
    by_cases hha : a ≤ h
    · have hall := hA (h - a) (by linarith) (by
        convert hfinl using 2; ring_nf)
      rcases j with i | i
      · rw [hre_l]; linarith [hall i]
      · rw [hre_r]; linarith [hall i]
    · push Not at hha
      exact absurd (hfinl.subset fun i (hi : 1 / 2 ≤ (ρ i).re) => by
        simp only [Set.mem_setOf_eq]; linarith) (infinite_re_ge_half fe hfe)


end GaloisForLFunctions.InfiniteRankWeilTheory
