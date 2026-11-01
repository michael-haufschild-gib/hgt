import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingCalculus
import GaloisForLFunctions.HeckeKreinToeplitz.TheWeilKernelIsKreinLangerOnTheFiniteStratum
import GaloisForLFunctions.HeckeKreinToeplitz.OneGridHidesTwoGridsDecide
import GaloisForLFunctions.ArithmeticResonanceTheory.TheAmplifierLaw
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheCollisionMassIsTheWaveNumber

/-!
# The coupling of a single two-prime lattice on the finite stratum

The inter-tower coupling of the minimal prime set `S = {p, q}` is `C(p^a, q^b)`. Unlike the coupling
of two disjoint lattices, it never comes close to the antidiagonal in a way that continuity can use:
`a log p + b log q → 0` is approached only polynomially (Baker), while the kernel varies at
exponential rate. We therefore read it spectrally.

On the finite stratum (finitely many zeros right of the line), Weil's kernel is a positive-definite
on-line part plus one hyperbolic pair `ω̄χ_ρ + ωχ_ρ^†` per right zero, with `χ_ρ(u) = u^{ρ̄−½}` and
`ω_ρ ≠ 0` (HKT `orbitKernel_eq_onLine_add_pairs`, AKLT `Wsummand_ne_zero_of_rightZero`). The coupling
of a pair is `ω̄(χ(u) − 1)(χ(v) − 1) + ω(χ^†(u) − 1)(χ^†(v) − 1)` (`coupling_pairKernel`). Along the
ray `(p^n, q^{mn})`, the product term is `Z_ρ^n` with `Z_ρ = χ_ρ(p q^m)`, of modulus
`e^{δ_ρ(log p + m log q)}`, `δ_ρ = Re ρ − ½`. It dominates every axial term and every reflected
term. For all but finitely many `m` the values `Z_ρ` are distinct (`exists_generic_direction`),
because two zeros alias in two directions only if `log p / log q` is rational. The top-modulus
part is then an almost periodic sum that would have to vanish (`coeff_eq_zero_of_tendsto`), which
contradicts `ω_ρ ≠ 0`.

**Theorem** (`riemannHypothesis_of_bounded_singleLatticeCoupling`). If the coupling of `K_ζ` on
`⟨p⟩ × ⟨q⟩` is bounded for nonnegative exponents and `ζ` has finitely many zeros right of the line,
then RH holds. Equivalently (`riemannHypothesis_or_infinite_of_bounded_singleLatticeCoupling`),
bounded single-lattice coupling leaves only RH or infinitely many off-line zeros.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx rightZeros rightZeros_zeta_eq_empty_iff)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-- The coupling of a hyperbolic pair kernel. -/
theorem coupling_pairKernel {G : Type*} [CommGroup G] (χ : G →* ℂ) (ω : ℂ) (u v : G) :
    coupling (pairKernel χ ω) u v =
      ω * ((χ u - 1) * (χ v - 1)) + conj ω * ((reflectChar χ u - 1) * (reflectChar χ v - 1)) := by
  simp only [coupling, pairKernel, map_mul, map_one]; ring

/-- The character `u ↦ u^{ρ̄ − ½}` attached to a right zero `ρ`. -/
abbrev rightChar (ρ : ℂ) : HeckeLattice →* ℂ := zeroChar (conj ρ)

theorem norm_rightChar (ρ : ℂ) (u : HeckeLattice) :
    ‖rightChar ρ u‖ = Real.exp ((ρ.re - 1 / 2) * scale heckeLogScale u) := by
  rw [rightChar, norm_logChar]; congr 2; simp

theorem norm_reflectChar_rightChar (ρ : ℂ) (u : HeckeLattice) :
    ‖reflectChar (rightChar ρ) u‖ = Real.exp (-((ρ.re - 1 / 2) * scale heckeLogScale u)) := by
  rw [reflectChar_apply, Complex.norm_conj, norm_rightChar, scale_inv]; ring_nf

theorem scale_primeElt_pow {p : ℕ} (hp : p.Prime) (m : ℕ) :
    scale heckeLogScale (primeElt hp ^ m) = m * Real.log p := by
  rw [← zpow_natCast, scale_zpow, scale_primeElt]; norm_cast

/-- The log-length `Λ_m = log p + m log q` of the direction `p q^m`. -/
theorem scale_direction {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (m : ℕ) :
    scale heckeLogScale (primeElt hp * primeElt hq ^ m) = Real.log p + m * Real.log q := by
  rw [scale_mul, scale_primeElt, scale_primeElt_pow]

theorem log_prime_pos {p : ℕ} (hp : p.Prime) : 0 < Real.log p :=
  Real.log_pos (by exact_mod_cast hp.one_lt)

/-- **Two zeros alias in at most one direction.** -/
theorem rightChar_direction_subsingleton {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ρ σ : ℂ} (hρσ : ρ ≠ σ) :
    {m : ℕ | rightChar ρ (primeElt hp * primeElt hq ^ m) =
      rightChar σ (primeElt hp * primeElt hq ^ m)}.Subsingleton := by
  intro m hm m' hm'
  simp only [Set.mem_setOf_eq, rightChar, logChar_apply, scale_direction hp hq] at hm hm'
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hm
  obtain ⟨k', hk'⟩ := Complex.exp_eq_exp_iff_exists_int.mp hm'
  set d : ℂ := conj ρ - conj σ with hd
  have hd0 : d ≠ 0 := by
    rw [hd, sub_ne_zero]; intro h; exact hρσ (by simpa using congrArg conj h)
  set L : ℝ := Real.log p + m * Real.log q
  set L' : ℝ := Real.log p + m' * Real.log q
  have hlp := log_prime_pos hp
  have hlq := log_prime_pos hq
  have hL : 0 < L := by positivity
  have h1 : d * L = k * (2 * Real.pi * I) := by
    rw [hd]; linear_combination hk
  have h2 : d * L' = k' * (2 * Real.pi * I) := by
    rw [hd]; linear_combination hk'
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, mul_eq_zero] at h1
    rcases h1 with h | h
    · exact hd0 h
    · exact hL.ne' (by exact_mod_cast h)
  have hc : ((k * L' : ℝ) : ℂ) * (2 * Real.pi * I) = ((k' * L : ℝ) : ℂ) * (2 * Real.pi * I) := by
    push_cast; linear_combination (-(L' : ℂ)) * h1 + (L : ℂ) * h2
  have hπ : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hreal : (k : ℝ) * L' = k' * L := by exact_mod_cast mul_right_cancel₀ hπ hc
  have hlin : ((k : ℝ) - k') * Real.log p = (k' * m - k * m') * Real.log q := by
    simp only [L, L'] at hreal; linarith
  by_cases hkk : k = k'
  · subst hkk
    have : (k : ℝ) * ((m : ℝ) - m') * Real.log q = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (by exact_mod_cast h) hk0
      · exact_mod_cast sub_eq_zero.mp h
    · exact absurd h hlq.ne'
  · exfalso
    have hirr := RHTower.irrational_log_ratio hq hp hpq.symm
    have hkk' : ((k : ℝ) - k') ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkk)
    apply hirr.ne_rat (((k' * m - k * m' : ℤ) : ℚ) / ((k - k' : ℤ) : ℚ))
    push_cast
    field_simp
    linarith

/-- **A generic direction.** For a finite set of zeros there is `m ≥ 1` such that the values
`χ_ρ(p q^m)` are pairwise distinct. -/
theorem exists_generic_direction {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (R : Finset ℂ) : ∃ m : ℕ, 1 ≤ m ∧
      Set.InjOn (fun ρ => rightChar ρ (primeElt hp * primeElt hq ^ m)) R := by
  classical
  set Bad : Set ℕ := {0} ∪ ⋃ x ∈ (R ×ˢ R).filter (fun x => x.1 ≠ x.2),
    {m : ℕ | rightChar x.1 (primeElt hp * primeElt hq ^ m) =
      rightChar x.2 (primeElt hp * primeElt hq ^ m)}
  have hfin : Bad.Finite := (Set.finite_singleton 0).union
    (Set.Finite.biUnion (Finset.finite_toSet _) fun x hx =>
      (rightChar_direction_subsingleton hp hq hpq (mem_filter.mp hx).2).finite)
  obtain ⟨m, hm⟩ := hfin.exists_notMem
  refine ⟨m, ?_, fun ρ hρ σ hσ heq => ?_⟩
  · by_contra h
    exact hm (Or.inl (by simpa using (Nat.lt_one_iff.mp (not_le.mp h))))
  · by_contra hne
    apply hm
    refine Or.inr (Set.mem_biUnion (x := (ρ, σ)) ?_ heq)
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hρ, hσ⟩, hne⟩

/-- **On the finite stratum, bounded single-lattice coupling forces RH.** -/
theorem riemannHypothesis_of_bounded_singleLatticeCoupling {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q) (hfin : (rightZeros zetaZeroConfig).Finite)
    (hbd : ∃ M : ℝ, ∀ a b : ℕ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M) :
    RiemannHypothesis := by
  classical
  obtain ⟨M, hM⟩ := hbd
  rw [← rightZeros_zeta_eq_empty_iff]
  by_contra hne
  set R := hfin.toFinset with hRdef
  have hRne : R.Nonempty := by
    rw [hRdef, Set.Finite.toFinset_nonempty]; exact Set.nonempty_iff_ne_empty.mpr hne
  have hRmem : ∀ ρ ∈ R, ρ ∈ rightZeros zetaZeroConfig := fun ρ h => hfin.mem_toFinset.mp h
  -- the weights and the decomposition
  set ω : ℂ → ℂ := fun ρ => conj (zetaZeroConfig.Wsummand (cx cubicSpline) (cx cubicSpline) ρ)
  have hω : ∀ ρ ∈ R, ω ρ ≠ 0 := fun ρ h => by
    simp only [ω, ne_eq, map_eq_zero]
    exact ArithmeticKreinLangerTheory.Wsummand_ne_zero_of_rightZero (hRmem ρ h)
  have hre : ∀ ρ ∈ R, 1 / 2 < ρ.re := fun ρ h => (hRmem ρ h).2
  set Kon := orbitKernel (onLineConfig zetaZeroConfig) cubicSpline
  have hdec : ∀ g, zetaKernel g = Kon g + ∑ ρ ∈ R, pairKernel (rightChar ρ) (ω ρ) g :=
    fun g => orbitKernel_eq_onLine_add_pairs SquareRootThreshold.temperedConfig_zetaZeroConfig
      cubicSpline_mem_realTests hfin g
  have hKon := isPosDefKernel_orbitKernel_onLine SquareRootThreshold.temperedConfig_zetaZeroConfig
    cubicSpline_mem_realTests (f := cubicSpline)
  -- the main sum is bounded
  set S : HeckeLattice → HeckeLattice → ℂ := fun u v =>
    ∑ ρ ∈ R, ω ρ * ((rightChar ρ u - 1) * (rightChar ρ v - 1))
  have hcoup : ∀ u v, coupling zetaKernel u v = coupling Kon u v + S u v +
      ∑ ρ ∈ R, conj (ω ρ) * ((reflectChar (rightChar ρ) u - 1) *
        (reflectChar (rightChar ρ) v - 1)) := fun u v => by
    rw [show zetaKernel = fun g => Kon g + ∑ ρ ∈ R, pairKernel (rightChar ρ) (ω ρ) g from
      funext hdec, coupling_add, coupling_sum]
    simp only [coupling_pairKernel, sum_add_distrib, S]; ring
  have hKb : ∀ u v, ‖coupling Kon u v‖ ≤ 4 * (Kon 1).re := fun u v => by
    have := hKon.norm_le
    unfold coupling
    calc ‖Kon (u * v) - Kon u - Kon v + Kon 1‖
        ≤ ‖Kon (u * v)‖ + ‖Kon u‖ + ‖Kon v‖ + ‖Kon 1‖ := by
          have e1 := norm_add_le (Kon (u * v) - Kon u - Kon v) (Kon 1)
          have e2 := norm_sub_le (Kon (u * v) - Kon u) (Kon v)
          have e3 := norm_sub_le (Kon (u * v)) (Kon u)
          linarith
      _ ≤ 4 * (Kon 1).re := by linarith [this (u * v), this u, this v, this 1]
  have hrefl : ∀ ρ ∈ R, ∀ a b : ℕ, ‖conj (ω ρ) * ((reflectChar (rightChar ρ) (primeElt hp ^ a) - 1) *
      (reflectChar (rightChar ρ) (primeElt hq ^ b) - 1))‖ ≤ 4 * ‖ω ρ‖ := fun ρ hρ a b => by
    have hδ : 0 < ρ.re - 1 / 2 := by linarith [hre ρ hρ]
    have hle : ∀ (r : ℕ) (hr : r.Prime) (c : ℕ), ‖reflectChar (rightChar ρ) (primeElt hr ^ c) - 1‖ ≤ 2 :=
      fun r hr c => by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_reflectChar_rightChar, scale_primeElt_pow, norm_one]
        have : Real.exp (-((ρ.re - 1 / 2) * (c * Real.log r))) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by
            have := mul_nonneg hδ.le (mul_nonneg (Nat.cast_nonneg c) (log_prime_pos hr).le)
            linarith)
        linarith
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := mul_le_mul (hle p hp a) (hle q hq b) (norm_nonneg _) (by norm_num)
    nlinarith [norm_nonneg (ω ρ)]
  set M' : ℝ := M + 4 * (Kon 1).re + ∑ ρ ∈ R, 4 * ‖ω ρ‖
  have hS : ∀ a b : ℕ, ‖S (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M' := fun a b => by
    have hc := hcoup (primeElt hp ^ a) (primeElt hq ^ b)
    have h1 : S (primeElt hp ^ a) (primeElt hq ^ b) = coupling zetaKernel (primeElt hp ^ a)
        (primeElt hq ^ b) - coupling Kon (primeElt hp ^ a) (primeElt hq ^ b) -
          ∑ ρ ∈ R, conj (ω ρ) * ((reflectChar (rightChar ρ) (primeElt hp ^ a) - 1) *
            (reflectChar (rightChar ρ) (primeElt hq ^ b) - 1)) := by rw [hc]; ring
    rw [h1]
    have e1 := norm_sub_le (coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b) -
      coupling Kon (primeElt hp ^ a) (primeElt hq ^ b)) (∑ ρ ∈ R, conj (ω ρ) *
        ((reflectChar (rightChar ρ) (primeElt hp ^ a) - 1) *
          (reflectChar (rightChar ρ) (primeElt hq ^ b) - 1)))
    have e2 := norm_sub_le (coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b))
      (coupling Kon (primeElt hp ^ a) (primeElt hq ^ b))
    have e3 := (norm_sum_le R _).trans (sum_le_sum fun ρ hρ => hrefl ρ hρ a b)
    linarith [hM a b, hKb (primeElt hp ^ a) (primeElt hq ^ b)]
  -- a generic direction and the top modulus
  obtain ⟨m, hm1, hinj⟩ := exists_generic_direction hp hq hpq R
  set g := primeElt hp * primeElt hq ^ m
  set Λ : ℝ := Real.log p + m * Real.log q
  have hΛg : scale heckeLogScale g = Λ := scale_direction hp hq m
  have hlp := log_prime_pos hp
  have hlq := log_prime_pos hq
  have hΛ : 0 < Λ := by positivity
  obtain ⟨ρ₀, hρ₀, hmax⟩ := R.exists_max_image (fun ρ => ρ.re - 1 / 2) hRne
  set δ := ρ₀.re - 1 / 2
  have hδ : 0 < δ := sub_pos.mpr (hre ρ₀ hρ₀)
  set r : ℝ := Real.exp (δ * Λ)
  have hr1 : 1 < r := Real.one_lt_exp_iff.mpr (mul_pos hδ hΛ)
  have hr0 : (0 : ℝ) < r := by positivity
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  set T := R.filter (fun ρ => ρ.re - 1 / 2 = δ)
  set X : ℂ → ℂ := fun ρ => rightChar ρ (primeElt hp)
  set W : ℂ → ℂ := fun ρ => rightChar ρ (primeElt hq ^ m)
  set Z : ℂ → ℂ := fun ρ => rightChar ρ g
  have hZXW : ∀ ρ, Z ρ = X ρ * W ρ := fun ρ => by simp only [Z, X, W, g, map_mul]
  -- the ray `(p^n, q^{mn})`
  have hray : ∀ n : ℕ, S (primeElt hp ^ n) (primeElt hq ^ (m * n)) =
      ∑ ρ ∈ R, ω ρ * (Z ρ ^ n - X ρ ^ n - W ρ ^ n + 1) := fun n => by
    refine sum_congr rfl fun ρ _ => ?_
    have e1 : rightChar ρ (primeElt hp ^ n) = X ρ ^ n := map_pow _ _ _
    have e2 : rightChar ρ (primeElt hq ^ (m * n)) = W ρ ^ n := by
      rw [pow_mul, map_pow]
    rw [e1, e2, hZXW, mul_pow]; ring
  -- norms of the scaled bases
  have hnormZ : ∀ ρ ∈ R, ‖Z ρ / r‖ = Real.exp ((ρ.re - 1 / 2 - δ) * Λ) := fun ρ _ => by
    rw [norm_div, norm_rightChar, hΛg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      ← Real.exp_sub]; ring_nf
  have hlt : ∀ x : ℝ, x < 0 → Real.exp x < 1 := fun x hx => Real.exp_lt_one_iff.mpr hx
  have hmaxδ : ∀ ρ ∈ R, ρ.re - 1 / 2 ≤ δ := fun ρ h => hmax ρ h
  have hX : ∀ ρ ∈ R, ‖X ρ / r‖ < 1 := fun ρ hρ => by
    rw [norm_div, norm_rightChar, scale_primeElt, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, div_lt_one hr0]
    refine Real.exp_lt_exp.mpr ?_
    have h1 : (ρ.re - 1 / 2) * Real.log p ≤ δ * Real.log p :=
      mul_le_mul_of_nonneg_right (hmaxδ ρ hρ) hlp.le
    have h2 : 0 < δ * (m * Real.log q) := mul_pos hδ (mul_pos (by exact_mod_cast hm1) hlq)
    simp only [Λ]; nlinarith
  have hW : ∀ ρ ∈ R, ‖W ρ / r‖ < 1 := fun ρ hρ => by
    rw [norm_div, norm_rightChar, scale_primeElt_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr0, div_lt_one hr0]
    refine Real.exp_lt_exp.mpr ?_
    have h1 : (ρ.re - 1 / 2) * (m * Real.log q) ≤ δ * (m * Real.log q) :=
      mul_le_mul_of_nonneg_right (hmaxδ ρ hρ) (mul_nonneg (Nat.cast_nonneg m) hlq.le)
    have h2 : 0 < δ * Real.log p := mul_pos hδ hlp
    simp only [Λ]; nlinarith
  have hone : ‖(1 : ℂ) / r‖ < 1 := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, div_lt_one hr0]
    exact hr1
  have hZlow : ∀ ρ ∈ R \ T, ‖Z ρ / r‖ < 1 := fun ρ hρ => by
    obtain ⟨hρR, hρT⟩ := mem_sdiff.mp hρ
    have hne : ρ.re - 1 / 2 ≠ δ := fun h => hρT (mem_filter.mpr ⟨hρR, h⟩)
    rw [hnormZ ρ hρR]
    exact hlt _ (mul_neg_of_neg_of_pos (by
      have := hmaxδ ρ hρR; exact sub_neg.mpr (lt_of_le_of_ne this hne)) hΛ)
  -- the scaled ray tends to zero
  have hpow : ∀ z : ℂ, ‖z‖ < 1 → Tendsto (fun n : ℕ => z ^ n) atTop (𝓝 0) := fun z hz =>
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have hscaled : Tendsto (fun n : ℕ => S (primeElt hp ^ n) (primeElt hq ^ (m * n)) / (r : ℂ) ^ n)
      atTop (𝓝 0) := by
    have hgeo := (tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hr0.le)
      (inv_lt_one_of_one_lt₀ hr1)).const_mul M'
    rw [mul_zero] at hgeo
    refine squeeze_zero_norm (fun n => ?_) hgeo
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0, inv_pow,
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hS n (m * n)) (by positivity)
  have hlower : Tendsto (fun n : ℕ => ∑ ρ ∈ R \ T, ω ρ * (Z ρ / r) ^ n -
      ∑ ρ ∈ R, ω ρ * ((X ρ / r) ^ n + (W ρ / r) ^ n - (1 / r) ^ n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ∑ ρ ∈ R \ T, ω ρ * (Z ρ / r) ^ n) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (R \ T) fun ρ hρ => (hpow _ (hZlow ρ hρ)).const_mul (ω ρ)
    have h2 : Tendsto (fun n : ℕ => ∑ ρ ∈ R, ω ρ * ((X ρ / r) ^ n + (W ρ / r) ^ n - (1 / r) ^ n))
        atTop (𝓝 0) := by
      simpa using tendsto_finsetSum R fun ρ hρ =>
        (((hpow _ (hX ρ hρ)).add (hpow _ (hW ρ hρ))).sub (hpow _ hone)).const_mul (ω ρ)
    simpa using h1.sub h2
  have htop : Tendsto (fun n : ℕ => ∑ ρ ∈ T, ω ρ * (Z ρ / r) ^ n) atTop (𝓝 0) := by
    have h := hscaled.sub hlower
    rw [sub_zero] at h
    refine h.congr fun n => ?_
    rw [hray n, sum_div]
    have hsplit : ∑ ρ ∈ R, ω ρ * (Z ρ / r) ^ n =
        ∑ ρ ∈ T, ω ρ * (Z ρ / r) ^ n + ∑ ρ ∈ R \ T, ω ρ * (Z ρ / r) ^ n := by
      rw [← sum_union (disjoint_sdiff), union_sdiff_of_subset (filter_subset _ _)]
    have hterm : ∀ ρ ∈ R, ω ρ * (Z ρ ^ n - X ρ ^ n - W ρ ^ n + 1) / (r : ℂ) ^ n =
        ω ρ * (Z ρ / r) ^ n - ω ρ * ((X ρ / r) ^ n + (W ρ / r) ^ n - (1 / r) ^ n) :=
      fun ρ _ => by
        simp only [div_pow, one_pow]
        field_simp
        ring
    rw [sum_congr rfl hterm, sum_sub_distrib, hsplit]
    ring
  -- the almost periodic top part must vanish
  have hunit : ∀ ρ ∈ T, ‖Z ρ / r‖ = 1 := fun ρ hρ => by
    obtain ⟨hρR, hρδ⟩ := mem_filter.mp hρ
    rw [hnormZ ρ hρR, hρδ, sub_self, zero_mul, Real.exp_zero]
  have hinjT : Set.InjOn (fun ρ => Z ρ / r) T := fun ρ hρ σ hσ h => by
    have h' : Z ρ = Z σ := by
      have := congrArg (· * (r : ℂ)) h
      simpa [div_mul_cancel₀ _ hrC] using this
    exact hinj (filter_subset _ _ hρ) (filter_subset _ _ hσ) h'
  have hzero := ArithmeticResonanceTheory.coeff_eq_zero_of_tendsto T ω (fun ρ => Z ρ / r)
    hunit hinjT htop
  have hρ₀T : ρ₀ ∈ T := mem_filter.mpr ⟨hρ₀, rfl⟩
  exact hω ρ₀ hρ₀ (hzero ρ₀ hρ₀T)

/-- **Bounded single-lattice coupling leaves only RH or infinitely many off-line zeros.** -/
theorem riemannHypothesis_or_infinite_of_bounded_singleLatticeCoupling {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hpq : p ≠ q)
    (hbd : ∃ M : ℝ, ∀ a b : ℕ, ‖coupling zetaKernel (primeElt hp ^ a) (primeElt hq ^ b)‖ ≤ M) :
    RiemannHypothesis ∨ (rightZeros zetaZeroConfig).Infinite := by
  rcases (rightZeros zetaZeroConfig).finite_or_infinite with h | h
  · exact Or.inl (riemannHypothesis_of_bounded_singleLatticeCoupling hp hq hpq h hbd)
  · exact Or.inr h

end GaloisForLFunctions.ArithmeticCouplingTheory
