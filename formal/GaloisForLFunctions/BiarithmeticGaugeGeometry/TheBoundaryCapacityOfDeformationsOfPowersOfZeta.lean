import GaloisForLFunctions.BiarithmeticGaugeGeometry.StrongMultiplicityOneForPowersOfZeta

/-!
# The Boundary Capacity of Deformations of Powers of ζ

A member `(F, Λ)` of `CompletedPositiveSystem κ d` has pole budget `κ` at `s = 1`; a boundary zero is
a zero of `Λ` on the line `Re s = 1` off the real axis. The collective capacity law bounds the total
boundary multiplicity at positive heights by `κ/2`. For members dominating `ζ^d`, the lattice of
`ζ^d` spends `d` units of the budget and cannot pay for boundary zeros.

* **Boundary capacity (`zetaPowDeformation_boundary_capacity`).** If `−F'/F + dζ'/ζ = 𝓛ν + E` with
  `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`, `σ_E < 1`, then for every finite set `Z` of positive
  heights `2 Σ_{t ∈ Z} ord_{1+it} Λ ≤ κ − d`. Either the abscissa of `ν` lies left of the line and the
  divisor of `Λ` on the line is that of `ζ^d`'s completion (no boundary zeros, by the prime number
  theorem), or it is the anchor `s = 1`, where the Abel–Gram law makes the jump
  `t ↦ ord_{1+it} Λ₀ − ord_{1+it} Λ` even positive definite with value `≤ κ − d` at `0` and
  `−ord_{1+it} Λ` elsewhere.
* **Density form (`zetaPowDeformation_boundary_law`, `latticeMember_boundary_law`).** It suffices
  that the perturbation be Abel-negligible on the line; for a member with `−F'/F = Σ b(n) n^{−s}`,
  `b ≥ 0`, that the deficit `D = Σ (dΛ(n) − b(n))⁺ n^{−s}` have zero Abel density at `1`,
  `(σ − 1) D(σ) → 0`. Then also the pole budget is at least the degree, `d ≤ κ`: the jump at `s = 1`
  is a positive-definite value. For `κ ≤ d + 1` there is no zero on `Re s = 1` off `s = 1`
  (`latticeMember_ne_zero_on_boundary`).

The capacity `κ/2` is therefore never attained by these classes when `d ≥ 1`, and the boundary
twists of `ζ` (`κ = 2r + 1`, `r` boundary zeros) are optimal.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open StripBochnerWeilForcing MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace)

/-- `ξ` does not vanish on the line `Re s = 1`. -/
theorem xi_one_add_mul_I_ne_zero (t : ℝ) : RHTower.xi (1 + (t : ℂ) * I) ≠ 0 := by
  have hs1 : (1 : ℝ) ≤ (1 + (t : ℂ) * I).re := by simp
  intro h
  rcases eq_or_ne t 0 with rfl | ht
  · simpa using RHTower.xi_ne_zero_of_real 1 (by simpa using h)
  · have hne : (1 + (t : ℂ) * I) ≠ 1 := fun h' => ht (by
      have := congrArg Complex.im h'; simpa using this)
    have hpos : 0 < (1 + (t : ℂ) * I).re := by simp
    exact riemannZeta_ne_zero_of_one_le_re hs1
      ((RHTower.xi_eq_zero_iff hpos hne).mp h)

/-- The base completion `(s(s−1))^{κ−d}(2ξ)^d` has order `κ − d` at `s = 1`. -/
theorem analyticOrderAt_zetaPow_base_one (κ d : ℕ) :
    analyticOrderAt (fun s : ℂ => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d) 1 =
      (κ - d : ℕ) := by
  have hZ := completedPositiveSystem_riemannZeta
  have hg : AnalyticAt ℂ (fun s : ℂ => s ^ (κ - d) * (2 * RHTower.xi s) ^ d) 1 :=
    ((analyticAt_id.pow _).mul ((hZ.entire_Λ.analyticAt 1).pow d))
  have hf : AnalyticAt ℂ (fun s : ℂ => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d) 1 :=
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).pow _).mul
      ((hZ.entire_Λ.analyticAt 1).pow d)
  refine hf.analyticOrderAt_eq_natCast.mpr ⟨_, hg, ?_, ?_⟩
  · simp only [one_pow, one_mul]
    exact pow_ne_zero d (mul_ne_zero two_ne_zero (by simpa using RHTower.xi_ne_zero_of_real 1))
  · exact Filter.Eventually.of_forall fun s => by simp only [smul_eq_mul, mul_pow]; ring

/-- **The boundary law of deformations of `ζ^d`.** Let `(F, Λ) ∈ CompletedPositiveSystem κ d` with
`−F'/F + dζ'/ζ = 𝓛ν + E`, `ν ≥ 0`, `E` holomorphic on `Re s > 1` and Abel-negligible on the line,
`(σ − 1) E(σ + it) → 0`. Then `d ≤ κ`, and for every finite set `Z` of positive heights
`2 Σ_{t ∈ Z} ord_{1+it} Λ ≤ κ − d`. -/
theorem zetaPowDeformation_boundary_law {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ}
    (hE : DifferentiableOn ℂ E {s : ℂ | (1 : ℝ) < s.re})
    (hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * E ((σ : ℂ) + (t : ℂ) * I))
      (𝓝[>] 1) (𝓝 0))
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (fun s => riemannZeta s ^ d) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ)
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) :
    d ≤ κ ∧ 2 * ∑ t ∈ Z, (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat ≤ κ - d := by
  have hZ0 := completedPositiveSystem_riemannZeta
  set Λ' : ℂ → ℂ := fun s => Λ s * (s * (s - 1)) ^ (d - κ) with hΛ'
  set Λ₀ : ℂ → ℂ := fun s => (s * (s - 1)) ^ (κ - d) * (2 * RHTower.xi s) ^ d with hΛ₀
  obtain ⟨c, -, -, hanchor, hrel, hint⟩ := zetaPowDeformation_orders_and_anchor hS hconv hE hagree
  -- the abscissa is at most `1`: beyond it the anchor would sit at a real zero of the base
  have hc : c ≤ 1 := by
    by_contra hgt
    push Not at hgt
    exact absurd (hanchor (by linarith) hgt).2 hgt.ne'
  have hmax : max c 1 = 1 := max_eq_right hc
  have hΛ'd : Differentiable ℂ Λ' := hS.entire_Λ.mul (by fun_prop)
  have hΛ₀d : Differentiable ℂ Λ₀ := zetaPow_base_differentiable κ d
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have htop := analyticOrderAt_ne_top_of_ne_zero hΛ'd (z₀ := 2)
    (mul_ne_zero (hS.ne_zero_of_one_lt_re h2) (pow_ne_zero _ (by norm_num)))
  have htop₀ := analyticOrderAt_ne_top_of_ne_zero hΛ₀d (z₀ := 2)
    (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (hZ0.ne_zero_of_one_lt_re h2)))
  have hrel1 : ∀ z : ℂ, (1 : ℝ) < z.re → Λ' z ≠ 0 → Λ₀ z ≠ 0 →
      logDeriv Λ₀ z - logDeriv Λ' z = GaloisForLFunctions.RHTower.complexLaplace ν z + E z :=
    fun z hz => hrel z (by rw [hmax]; exact hz)
  have hint1 : ∀ z : ℂ, (1 : ℝ) < z.re →
      Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ))) :=
    fun z hz => hint z (lt_of_le_of_lt hc hz)
  have hord1 : (analyticOrderAt Λ₀ ((1 : ℝ) : ℂ)).toNat = κ - d := by
    rw [Complex.ofReal_one, analyticOrderAt_zetaPow_base_one]; rfl
  -- the jump at `s = 1` is nonnegative: no pole budget, no excess
  have hdκ : d ≤ κ := by
    by_contra hlt
    push Not at hlt
    have hD0 := (jump_isEvenPosDef_of_rel hΛ'd hΛ₀d htop htop₀ (x₀ := 1) hrel1 hEt
      hint1).apply_zero_nonneg
    simp only [Complex.ofReal_zero, zero_mul, add_zero, hord1, show κ - d = 0 by omega,
      Nat.cast_zero, zero_sub, Left.nonneg_neg_iff, Nat.cast_nonpos] at hD0
    have hz : Λ' ((1 : ℝ) : ℂ) = 0 := by
      simp [hΛ', zero_pow (show d - κ ≠ 0 by omega)]
    have h1 := (hΛ'd.analyticAt _).analyticOrderAt_eq_zero.not.mpr (not_not.mpr hz)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (htop ((1 : ℝ) : ℂ))
    rw [← hm, ENat.toNat_coe] at hD0
    rw [← hm, hD0] at h1
    exact h1 rfl
  refine ⟨hdκ, ?_⟩
  -- `Λ₀` has no zero on `Re s = 1` off the real axis
  have hline : ∀ t : ℝ, t ≠ 0 → Λ₀ (((1 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t ht
    have hw0 : ((1 : ℝ) : ℂ) + (t : ℂ) * I ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this
    have hw1 : ((1 : ℝ) : ℂ) + (t : ℂ) * I - 1 ≠ 0 := fun h => ht (by
      have := congrArg Complex.im h; simpa using this)
    refine mul_ne_zero (pow_ne_zero _ (mul_ne_zero hw0 hw1)) (pow_ne_zero _ (mul_ne_zero
      two_ne_zero ?_))
    simpa using xi_one_add_mul_I_ne_zero t
  -- on the line, the orders of `Λ'` and `Λ` agree off the real axis
  have hordline : ∀ t : ℝ, t ≠ 0 → analyticOrderAt Λ' (((1 : ℝ) : ℂ) + (t : ℂ) * I) =
      analyticOrderAt Λ (((1 : ℝ) : ℂ) + (t : ℂ) * I) := by
    intro t ht
    have hw : (((1 : ℝ) : ℂ) + (t : ℂ) * I) * (((1 : ℝ) : ℂ) + (t : ℂ) * I - 1) ≠ 0 := by
      refine mul_ne_zero (fun h => ?_) (fun h => ht ?_)
      · have := congrArg Complex.re h; simp at this
      · have := congrArg Complex.im h; simpa using this
    rw [show Λ' = Λ * fun s => (s * (s - 1)) ^ (d - κ) from rfl,
      analyticOrderAt_mul (hS.entire_Λ.analyticAt _) (by fun_prop),
      (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s * (s - 1)) ^ (d - κ)) _).analyticOrderAt_eq_zero.mpr
        (pow_ne_zero _ hw), add_zero]
  have hcap := sum_jump_le_of_rel hΛ'd hΛ₀d htop htop₀ (x₀ := 1) hrel1 hEt hint1 hline hZ
  rw [hord1] at hcap
  have hsum : ∑ t ∈ Z, ((analyticOrderAt Λ' (((1 : ℝ) : ℂ) + (t : ℂ) * I)).toNat : ℝ) =
      ((∑ t ∈ Z, (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun t ht => ?_
    have h := hordline t (hZ t ht).ne'
    rw [Complex.ofReal_one] at h
    rw [h]
  rw [hsum] at hcap
  have hnn : (0 : ℝ) ≤ (analyticOrderAt Λ' ((1 : ℝ) : ℂ)).toNat := Nat.cast_nonneg _
  have : ((2 * ∑ t ∈ Z, (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat : ℕ) : ℝ) ≤
      ((κ - d : ℕ) : ℝ) := by push_cast [hdκ] at hcap ⊢; linarith
  exact_mod_cast this

/-- **Boundary capacity of deformations of `ζ^d`.** If `(F, Λ) ∈ CompletedPositiveSystem κ d` and
`−F'/F + dζ'/ζ = 𝓛ν + E` with `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`, `σ_E < 1`, then for every
finite set `Z` of positive heights `2 Σ_{t ∈ Z} ord_{1+it} Λ ≤ κ − d`. -/
theorem zetaPowDeformation_boundary_capacity {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (fun s => riemannZeta s ^ d) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ)
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) :
    2 * ∑ t ∈ Z, (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat ≤ κ - d :=
  (zetaPowDeformation_boundary_law hS hconv
    (hE.mono fun s (hs : (1 : ℝ) < s.re) => show σE < s.re by linarith)
    (tendsto_sub_mul_of_differentiableOn hσE hE) hagree hZ).2

/-- The deficit of nonnegative coefficients against `dΛ` converges absolutely on `Re s > 1`. -/
theorem abscissaOfAbsConv_relDeficit_vonMangoldt_le_one (d : ℕ) {b : ℕ → ℝ}
    (hb : ∀ n, 0 ≤ b n) :
    LSeries.abscissaOfAbsConv
      (fun n => (relDeficit (fun n => d * ArithmeticFunction.vonMangoldt n) b n : ℂ)) ≤ 1 :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    summable_norm_term_of_le (relDeficit_nonneg _ b)
      (relDeficit_le (fun n => mul_nonneg (Nat.cast_nonneg d) ArithmeticFunction.vonMangoldt_nonneg)
        hb)
      (LSeriesSummable_of_abscissaOfAbsConv_lt_re
        (lt_of_le_of_lt (abscissaOfAbsConv_zeta_pow_le_one d)
          (by rw [Complex.ofReal_re]; exact_mod_cast hy)))

/-- **The boundary law of arithmetic members.** If `(F, Λ) ∈ CompletedPositiveSystem κ d` with
`−F'/F = Σ b(n) n^{−s}`, `b ≥ 0`, and the deficit `D = Σ (dΛ(n) − b(n))⁺ n^{−s}` has zero Abel
density at `s = 1`, `(σ − 1) D(σ) → 0`, then the pole budget is at least the degree, `d ≤ κ`, and
`2 Σ_{t ∈ Z} ord_{1+it} Λ ≤ κ − d` for every finite set `Z` of positive heights. -/
theorem latticeMember_boundary_law {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hres : Tendsto (fun σ : ℝ => (σ - 1) * (LSeries
      (fun n => (relDeficit (fun n => d * ArithmeticFunction.vonMangoldt n) b n : ℂ)) (σ : ℂ)).re)
      (𝓝[>] 1) (𝓝 0))
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) :
    d ≤ κ ∧ 2 * ∑ t ∈ Z, (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat ≤ κ - d := by
  set a : ℕ → ℝ := fun n => d * ArithmeticFunction.vonMangoldt n with hadef
  have ha : ∀ n, 0 ≤ a n := fun n =>
    mul_nonneg (Nat.cast_nonneg d) ArithmeticFunction.vonMangoldt_nonneg
  have hdabs := abscissaOfAbsConv_relDeficit_vonMangoldt_le_one d hb
  set D : ℂ → ℂ := LSeries (fun n => (relDeficit a b n : ℂ)) with hDdef
  have hE : DifferentiableOn ℂ (fun s => (((b 1 - a 1 : ℝ)) : ℂ) - D s) {s : ℂ | (1 : ℝ) < s.re} :=
    fun s hs => ((differentiableAt_const _).sub (LSeries_hasDerivAt (lt_of_le_of_lt hdabs
      (by exact_mod_cast hs))).differentiableAt).differentiableWithinAt
  have hEt : ∀ t : ℝ, Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) *
      ((((b 1 - a 1 : ℝ)) : ℂ) - D ((σ : ℂ) + (t : ℂ) * I))) (𝓝[>] 1) (𝓝 0) := by
    intro t
    have h1 : Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * (((b 1 - a 1 : ℝ)) : ℂ)) (𝓝[>] 1)
        (𝓝 0) := by
      have h : Continuous fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * (((b 1 - a 1 : ℝ)) : ℂ) := by fun_prop
      have h' := (h.tendsto (1 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
      simpa using h'
    have h2 := tendsto_sub_mul_LSeries_of_residue_zero (relDeficit_nonneg a b) hdabs hres t
    have h3 := h1.sub h2
    rw [sub_zero] at h3
    exact h3.congr fun σ => by simp only [hDdef]; ring
  obtain ⟨hmass, hsplit⟩ := relMember_primeMass_split ha hb (abscissaOfAbsConv_zeta_pow_le_one d)
    habs hL (F₀ := fun w => riemannZeta w ^ d) (fun s hs => neg_logDeriv_zeta_pow_eq_LSeries d hs)
  exact zetaPowDeformation_boundary_law hS hmass hE hEt hsplit hZ

/-- **Boundary capacity of arithmetic members** with deficit of abscissa `< 1`. -/
theorem latticeMember_boundary_capacity {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hdef : LSeries.abscissaOfAbsConv
      (fun n => (relDeficit (fun n => d * ArithmeticFunction.vonMangoldt n) b n : ℂ)) <
        (1 : ℝ))
    {Z : Finset ℝ} (hZ : ∀ z ∈ Z, 0 < z) :
    2 * ∑ t ∈ Z, (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat ≤ κ - d :=
  (latticeMember_boundary_law hS hb habs hL (tendsto_residue_zero_of_abscissa_lt hdef) hZ).2

/-- **No boundary zeros below the second unit of budget.** An arithmetic member of
`CompletedPositiveSystem κ d` with `κ ≤ d + 1` whose deficit against `dΛ` has zero Abel density at
`s = 1` does not vanish on `Re s = 1` off the real axis. -/
theorem latticeMember_ne_zero_on_boundary {κ d : ℕ} {F Λ : ℂ → ℂ}
    (hS : CompletedPositiveSystem κ d F Λ) (hκ : κ ≤ d + 1) {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n)
    (habs : LSeries.abscissaOfAbsConv (fun n => (b n : ℂ)) ≤ 1)
    (hL : ∀ s : ℂ, 1 < s.re → -logDeriv F s = LSeries (fun n => (b n : ℂ)) s)
    (hres : Tendsto (fun σ : ℝ => (σ - 1) * (LSeries
      (fun n => (relDeficit (fun n => d * ArithmeticFunction.vonMangoldt n) b n : ℂ)) (σ : ℂ)).re)
      (𝓝[>] 1) (𝓝 0))
    {t : ℝ} (ht : t ≠ 0) : Λ (1 + (t : ℂ) * I) ≠ 0 := by
  -- reduce to a positive height by conjugation symmetry
  wlog htpos : 0 < t generalizing t
  · have hneg : 0 < -t := by
      rcases lt_or_gt_of_ne ht with h | h
      · linarith
      · exact absurd h htpos
    intro h0
    refine this (t := -t) (neg_ne_zero.mpr ht) hneg ?_
    have hc : (1 + ((-t : ℝ) : ℂ) * I) = starRingEnd ℂ (1 + (t : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [hc, hS.conj_Λ, h0, map_zero]
  have hcap := (latticeMember_boundary_law hS hb habs hL hres (Z := {t})
    (by simpa using htpos)).2
  rw [Finset.sum_singleton] at hcap
  intro h0
  have h1 : 1 ≤ (analyticOrderAt Λ (1 + (t : ℂ) * I)).toNat := by
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hS.orderAt_ne_top (1 + (t : ℂ) * I))
    have hne0 : analyticOrderAt Λ (1 + (t : ℂ) * I) ≠ 0 := fun hz =>
      ((hS.analyticOnNhd_univ _ (mem_univ _)).analyticOrderAt_eq_zero.mp hz) h0
    rw [← hm] at hne0 ⊢
    rw [ENat.toNat_coe]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)
  omega

end GaloisForLFunctions.BiarithmeticGaugeGeometry
