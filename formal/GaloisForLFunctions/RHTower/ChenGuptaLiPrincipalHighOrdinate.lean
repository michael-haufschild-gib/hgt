import GaloisForLFunctions.RHTower.ChenGuptaLiPrincipalContour
import GaloisForLFunctions.RHTower.ChenGuptaLiMollifierBound
import GaloisForLFunctions.RHTower.LaplaceTransformMomentDerivative
import GaloisForLFunctions.HTGeometry.GammaVerticalStripDecay
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# Chen--Gupta--Li principal residue at high ordinate

This closes the high-ordinate principal-residue estimate used after CGL
equation (12.1).  The bound is uniform in the conductor and in the zero's
real part throughout the critical strip.  Uniformity near `Re ρ = 1` comes
from shifting `Γ(1 - ρ)` once and paying the denominator `|1 - ρ|`, which is
at least the absolute ordinate.
-/

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The finite Euler residue of a principal Dirichlet `L`-function has norm
at most one, uniformly in its modulus. -/
theorem cglPrincipalLFunctionResidue_norm_le_one (q : ℕ) :
    ‖cglPrincipalLFunctionResidue q‖ ≤ 1 := by
  classical
  unfold cglPrincipalLFunctionResidue
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) ?_
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
  have hpinv0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hpinv1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpone
  have hcast : (1 - (p : ℂ)⁻¹) = ((1 - (p : ℝ)⁻¹ : ℝ) : ℂ) := by
    norm_num
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

/-- CGL's principal Gamma residue has one conductor- and abscissa-uniform
polynomial-times-exponential bound at absolute ordinate at least one. -/
theorem exists_cglPrincipalPole_Gamma_norm_le_polyExp :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ {q : ℕ}
      (z : CGLPrincipalCriticalStripLZero q), 1 ≤ |z.point.im| →
      ‖Complex.Gamma (cglPrincipalPole z)‖ ≤
        C * |z.point.im| ^ N * Real.exp (-(Real.pi * |z.point.im| / 2)) := by
  obtain ⟨C, N, hC, hGamma⟩ :=
    exists_bound_norm_Gamma_vertical_strip (a := (1 : ℝ)) (by norm_num) (3 / 2 : ℝ)
  refine ⟨C, N, hC, ?_⟩
  intro q z ht
  let w : ℂ := cglPrincipalPole z
  have hwre0 : 0 < w.re := cglPrincipalPole_re_pos z
  have hwre_le : w.re ≤ 1 / 2 := by
    dsimp [w]
    unfold cglPrincipalPole
    simp only [Complex.sub_re, Complex.one_re]
    linarith [z.half_le]
  have hwim : w.im = -z.point.im := by
    dsimp [w]
    simp [cglPrincipalPole]
  have hwabs : |w.im| = |z.point.im| := by rw [hwim, abs_neg]
  have hshift_re_low : (1 : ℝ) ≤ (w + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hshift_re_high : (w + 1).re ≤ (3 / 2 : ℝ) := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hshift : w + 1 = (((w + 1).re : ℝ) : ℂ) + (w.im : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
  have hhigh : ‖Complex.Gamma (w + 1)‖ ≤
      C * |w.im| ^ N * Real.exp (-(Real.pi * |w.im| / 2)) := by
    rw [hshift]
    exact hGamma (w + 1).re w.im hshift_re_low hshift_re_high (by simpa [hwabs] using ht)
  have hw0 : w ≠ 0 := by
    intro h
    have := hwre0
    rw [h] at this
    norm_num at this
  have hnormw : 1 ≤ ‖w‖ := by
    calc
      1 ≤ |w.im| := by simpa [hwabs] using ht
      _ ≤ ‖w‖ := abs_im_le_norm w
  have hrec := congrArg norm (Complex.Gamma_add_one w hw0)
  rw [norm_mul] at hrec
  have hlow : ‖Complex.Gamma w‖ ≤ ‖Complex.Gamma (w + 1)‖ := by
    rw [hrec]
    nlinarith [norm_nonneg w, norm_nonneg (Complex.Gamma w)]
  calc
    ‖Complex.Gamma (cglPrincipalPole z)‖ = ‖Complex.Gamma w‖ := rfl
    _ ≤ ‖Complex.Gamma (w + 1)‖ := hlow
    _ ≤ C * |w.im| ^ N * Real.exp (-(Real.pi * |w.im| / 2)) := hhigh
    _ = C * |z.point.im| ^ N * Real.exp (-(Real.pi * |z.point.im| / 2)) := by rw [hwabs]

/-- The exact regularized CGL principal Mellin residue has a quantitative
high-ordinate bound, uniform in conductor and critical-strip abscissa. -/
theorem cglPrincipalRegularizedMellinFactor_at_principalPole_norm_le_polyExp :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (X q : ℕ)
      (z : CGLPrincipalCriticalStripLZero q), 1 ≤ |z.point.im| →
      ‖cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z)‖ ≤
        (X + 1 : ℕ) *
          (C * |z.point.im| ^ N * Real.exp (-(Real.pi * |z.point.im| / 2))) := by
  obtain ⟨C, N, hC, hGamma⟩ := exists_cglPrincipalPole_Gamma_norm_le_polyExp
  refine ⟨C, N, hC, ?_⟩
  intro X q z ht
  have hM : ‖zeroDetectionMobiusPolynomial X (q + 1) z.character 1‖ ≤ (X + 1 : ℕ) := by
    simpa using norm_zeroDetectionMobiusPolynomial_le_cutoff X (q + 1) z.character
      ⟨1, by norm_num⟩
  have hE := cglPrincipalLFunctionResidue_norm_le_one q
  have hG := hGamma z ht
  rw [cglPrincipalRegularizedMellinFactor_at_principalPole, norm_mul, norm_mul]
  calc
    ‖Complex.Gamma (cglPrincipalPole z)‖ *
          ‖zeroDetectionMobiusPolynomial X (q + 1) z.character 1‖ *
        ‖cglPrincipalLFunctionResidue q‖ ≤
      ‖Complex.Gamma (cglPrincipalPole z)‖ * (X + 1 : ℕ) * 1 := by
        gcongr
    _ ≤ (C * |z.point.im| ^ N * Real.exp (-(Real.pi * |z.point.im| / 2))) *
        (X + 1 : ℕ) * 1 := by
      gcongr
    _ = (X + 1 : ℕ) *
        (C * |z.point.im| ^ N * Real.exp (-(Real.pi * |z.point.im| / 2))) := by ring

/-- For fixed detector length, the principal CGL residue is uniformly below
every positive threshold at sufficiently large absolute ordinate. -/
theorem cglPrincipalRegularizedMellinFactor_at_principalPole_eventually_lt
    (X : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ {q : ℕ} (z : CGLPrincipalCriticalStripLZero q),
      T ≤ |z.point.im| →
      ‖cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z)‖ < η := by
  obtain ⟨C, N, hC, hbound⟩ :=
    cglPrincipalRegularizedMellinFactor_at_principalPole_norm_le_polyExp
  have hδ : 0 < Real.pi / 2 := by positivity
  have hcore := tendsto_pow_mul_exp_neg_scaled N hδ
  have hlim : Tendsto (fun t : ℝ =>
      (X + 1 : ℕ) * (C * t ^ N * Real.exp (-(Real.pi * t / 2)))) atTop (nhds 0) := by
    have hscaled := hcore.const_mul ((X + 1 : ℕ) * C)
    rw [mul_zero] at hscaled
    convert hscaled using 1
    funext t
    ring_nf
  have hevent : ∀ᶠ t : ℝ in atTop,
      (X + 1 : ℕ) * (C * t ^ N * Real.exp (-(Real.pi * t / 2))) < η :=
    (tendsto_order.1 hlim).2 η hη
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hevent
  refine ⟨max T₀ 1, le_max_right _ _, ?_⟩
  intro q z ht
  have ht1 : 1 ≤ |z.point.im| := le_trans (le_max_right T₀ 1) ht
  have hmajor := hbound X q z ht1
  exact hmajor.trans_lt (hT₀ |z.point.im| (le_trans (le_max_left T₀ 1) ht))

/-- CGL Section 12.1's implication: if the principal residue retains any
fixed positive size, its zero ordinate belongs to one uniform bounded head. -/
theorem cglPrincipalRegularizedMellinFactor_large_forces_bounded_ordinate
    (X : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ {q : ℕ} (z : CGLPrincipalCriticalStripLZero q),
      η ≤ ‖cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z)‖ →
      |z.point.im| < T := by
  obtain ⟨T, hT, hsmall⟩ :=
    cglPrincipalRegularizedMellinFactor_at_principalPole_eventually_lt X hη
  refine ⟨T, hT, ?_⟩
  intro q z hlarge
  by_contra hnot
  have hTz : T ≤ |z.point.im| := le_of_not_gt hnot
  exact (not_lt_of_ge hlarge) (hsmall z hTz)

/-- **CGL Section 12.1, logarithmic principal head.**  The principal residue is
uniformly smaller than a fixed positive threshold once the ordinate exceeds a
logarithmic function of the detector length.  Both constants are independent
of the modulus and of the certified zero.

The proof is non-asymptotic: split the Gamma exponential into two equal
halves, absorb the polynomial factor by `t^N exp (-δ t) ≤ N! / δ^N`, and use
the second half to pay the factor `X + 1`. -/
theorem exists_cglPrincipalRegularizedMellinFactor_logarithmic_head
    {η : ℝ} (hη : 0 < η) :
    ∃ A K : ℝ, 0 < A ∧ 1 ≤ K ∧ ∀ (X q : ℕ)
      (z : CGLPrincipalCriticalStripLZero q),
      1 + A * Real.log (K * ((X : ℝ) + 1)) ≤ |z.point.im| →
      ‖cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z)‖ < η := by
  obtain ⟨C, N, hC, hbound⟩ :=
    cglPrincipalRegularizedMellinFactor_at_principalPole_norm_le_polyExp
  let δ : ℝ := Real.pi / 4
  let D : ℝ := C * (N.factorial : ℝ) / δ ^ N
  let K : ℝ := D / η + 1
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  have hK : 1 ≤ K := by
    dsimp [K]
    have hratio : 0 ≤ D / η := div_nonneg hD hη.le
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  refine ⟨δ⁻¹, K, inv_pos.mpr hδ, hK, ?_⟩
  intro X q z ht
  let t : ℝ := |z.point.im|
  have hX : 0 < (X : ℝ) + 1 := by positivity
  have harg : 0 < K * ((X : ℝ) + 1) := mul_pos hKpos hX
  have ht1 : 1 ≤ t := by
    have hlog : 0 ≤ Real.log (K * ((X : ℝ) + 1)) :=
      Real.log_nonneg (by nlinarith [hK])
    have hA : 0 ≤ δ⁻¹ := (inv_pos.mpr hδ).le
    dsimp [t]
    nlinarith [mul_nonneg hA hlog]
  have hraw := hbound X q z ht1
  have hraw' :
      ‖cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z)‖ ≤
        ((X : ℝ) + 1) *
          (C * t ^ N * Real.exp (-(Real.pi * t / 2))) := by
    simpa only [Nat.cast_add, Nat.cast_one, t] using hraw
  have hpow := GaloisForLFunctions.RHTower.pow_mul_exp_neg_le
    (δ := δ) (u := t) hδ (by positivity : 0 ≤ t) N
  have hsplit : Real.exp (-(Real.pi * t / 2)) =
      Real.exp (-δ * t) * Real.exp (-δ * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [δ]
    ring
  have hpoly : C * t ^ N * Real.exp (-(Real.pi * t / 2)) ≤
      D * Real.exp (-δ * t) := by
    rw [hsplit]
    dsimp [D]
    calc
      C * t ^ N * (Real.exp (-δ * t) * Real.exp (-δ * t)) =
          C * (t ^ N * Real.exp (-δ * t)) * Real.exp (-δ * t) := by ring
      _ ≤ C * ((N.factorial : ℝ) / δ ^ N) * Real.exp (-δ * t) := by
        gcongr
      _ = (C * (N.factorial : ℝ) / δ ^ N) * Real.exp (-δ * t) := by ring
  have hlog_le : Real.log (K * ((X : ℝ) + 1)) ≤ δ * t := by
    have hsmall : δ⁻¹ * Real.log (K * ((X : ℝ) + 1)) ≤ t := by
      change 1 + δ⁻¹ * Real.log (K * ((X : ℝ) + 1)) ≤ t at ht
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsmall hδ.le
    calc
      Real.log (K * ((X : ℝ) + 1)) =
          δ * (δ⁻¹ * Real.log (K * ((X : ℝ) + 1))) := by
            field_simp
      _ ≤ δ * t := hmul
  have hexp : Real.exp (-δ * t) ≤ (K * ((X : ℝ) + 1))⁻¹ := by
    calc
      Real.exp (-δ * t) ≤ Real.exp (-Real.log (K * ((X : ℝ) + 1))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = (K * ((X : ℝ) + 1))⁻¹ := by
        rw [Real.exp_neg, Real.exp_log harg]
  have hmajor : ((X : ℝ) + 1) *
        (C * t ^ N * Real.exp (-(Real.pi * t / 2))) ≤ D / K := by
    calc
      ((X : ℝ) + 1) * (C * t ^ N * Real.exp (-(Real.pi * t / 2))) ≤
          ((X : ℝ) + 1) * (D * Real.exp (-δ * t)) := by gcongr
      _ ≤ ((X : ℝ) + 1) * (D * (K * ((X : ℝ) + 1))⁻¹) := by gcongr
      _ = D / K := by
        field_simp
  have hDK : D / K < η := by
    rw [div_lt_iff₀ hKpos]
    dsimp [K]
    field_simp [hη.ne']
    nlinarith
  exact (hraw'.trans hmajor).trans_lt hDK

/-- Large principal residues therefore lie in one logarithmic ordinate head,
with constants uniform in the modulus and the detector length. -/
theorem cglPrincipalRegularizedMellinFactor_large_forces_logarithmic_ordinate
    {η : ℝ} (hη : 0 < η) :
    ∃ A K : ℝ, 0 < A ∧ 1 ≤ K ∧ ∀ (X q : ℕ)
      (z : CGLPrincipalCriticalStripLZero q),
      η ≤ ‖cglPrincipalRegularizedMellinFactor X q z (cglPrincipalPole z)‖ →
      |z.point.im| < 1 + A * Real.log (K * ((X : ℝ) + 1)) := by
  obtain ⟨A, K, hA, hK, hsmall⟩ :=
    exists_cglPrincipalRegularizedMellinFactor_logarithmic_head hη
  refine ⟨A, K, hA, hK, ?_⟩
  intro X q z hlarge
  by_contra hnot
  have ht : 1 + A * Real.log (K * ((X : ℝ) + 1)) ≤ |z.point.im| :=
    le_of_not_gt hnot
  exact (not_lt_of_ge hlarge) (hsmall X q z ht)

end

end RHTower
