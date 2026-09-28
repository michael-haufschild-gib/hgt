import GaloisForLFunctions.RHTower.ChronologicalGrowingMomentSource
import GaloisForLFunctions.RHTower.ChronologicalTailMellin
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The signed projection formula and the harmonic channel

Keep the Gram rows of `ChronologicalGrowingMomentSource`.  For `u > 0`, with `x_k = k/N`,
`M = ⌊N/2⌋`,

* `z_N(u) = Σ_{M < k ≤ N} v(x_k) h(u x_k)`, `d_N(u) = G_N⁻¹ z_N(u)`,
* `q_N(u, x) = v(x) · d_N(u)` (least-squares projection of `h(u ·)` on the tail samples),
* `Ψ_N(u) = e^{-u/N} + τ · d_N(u)`,

the actual residual satisfies the finite identity

  `r_N(u/N) = Ψ_N(u) + Σ_{k ≤ M} μ(k) [h(u x_k) - q_N(u, x_k)]`        (D)

since `G_N` is symmetric: the tail sum is `c_N · z_N = (G_N c_N) · d_N = b_N · d_N`.

Removing the `x⁻¹` channel `d_{-1}` and writing `Φ_N(u, x) = h(ux) - d_0(u) - Σ_j d_j(u) x^{2j-1}`
(with the analytic value `h(0) = 1/2`), finite Abel summation against the Mertens function
`A(y) = Σ_{k ≤ y} μ(k)` gives

  `r_N(u/N) = Ψ_N(u) - N H_M d_{-1}(u) + A(M) Φ_N(u, M/N) - ∫_0^{M/N} A(Nx) ∂_x Φ_N(u, x) dx`,  (E)

`H_M = Σ_{k ≤ M} μ(k)/k`.  Every term is bounded and measurable in `u`, hence square integrable
on `[0, log N]`.
-/

open MeasureTheory Set Filter ArithmeticFunction
open scoped Topology Moebius
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-! ### Identity (D) -/

/-- The tail heat vector `z_N(u) = Σ_{M < k ≤ N} v(k/N) h(u k/N)`. -/
def gmZ (m N : ℕ) (u : ℝ) (i : Fin (m + 2)) : ℝ :=
  ∑ k ∈ Finset.Ioc (N / 2) N, gmVec m N k i * fusionBoseDefect (u * ((k : ℝ) / N))

/-- `d_N(u) = G_N⁻¹ z_N(u)`. -/
def gmD (m N : ℕ) (u : ℝ) : Fin (m + 2) → ℝ := (gmGram m N)⁻¹.mulVec (gmZ m N u)

/-- The projection `q_N(u, x) = v(x) · d_N(u)`. -/
def gmQ (m N : ℕ) (u x : ℝ) : ℝ := ∑ i, x ^ gmExp m i * gmD m N u i

/-- `Ψ_N(u) = e^{-u/N} + τ · d_N(u)`. -/
def gmPsi (m N : ℕ) (u : ℝ) : ℝ := Real.exp (-(u / N)) + ∑ i, gmTarget m N i * gmD m N u i

theorem gmGram_symm (m N : ℕ) (i j : Fin (m + 2)) : gmGram m N i j = gmGram m N j i := by
  simp only [gmGram, mul_comm]

theorem dotProduct_gmGram_mulVec_comm (m N : ℕ) (x y : Fin (m + 2) → ℝ) :
    ∑ i, x i * (gmGram m N).mulVec y i = ∑ i, (gmGram m N).mulVec x i * y i := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [gmGram_symm m N j i]; ring

/-- **The signed projection formula (D).** -/
theorem heatError_gmRow_signed {m N : ℕ} (h : IsUnit (gmGram m N).det) {u : ℝ} :
    chronologicalHeatError (gmRow m N) N (u / N) =
      gmPsi m N u + ∑ k ∈ Finset.Ioc 0 (N / 2),
        ((μ k : ℤ) : ℝ) * (fusionBoseDefect (u * ((k : ℝ) / N)) - gmQ m N u ((k : ℝ) / N)) := by
  have hMN : N / 2 ≤ N := Nat.div_le_self N 2
  have harg : ∀ k : ℕ, (k : ℝ) * (u / N) = u * ((k : ℝ) / N) := fun k => by ring
  rw [chronologicalHeatError, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le (N / 2)) hMN]
  -- head
  have hhead : ∑ k ∈ Finset.Ioc 0 (N / 2), gmRow m N k * fusionBoseDefect (k * (u / N)) =
      ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * fusionBoseDefect (u * ((k : ℝ) / N)) :=
    Finset.sum_congr rfl fun k hk => by
      obtain ⟨hk0, hkM⟩ := Finset.mem_Ioc.mp hk
      rw [gmRow, if_neg hk0.ne', if_pos hkM, harg]
  -- tail
  have htail : ∑ k ∈ Finset.Ioc (N / 2) N, gmRow m N k * fusionBoseDefect (k * (u / N)) =
      ∑ i, gmCoeff m N i * gmZ m N u i := by
    simp only [gmZ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨hkM, hkN⟩ := Finset.mem_Ioc.mp hk
    rw [gmRow, if_neg (by omega), if_neg (by omega), if_pos hkN, gmTail, harg, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hGd : (gmGram m N).mulVec (gmD m N u) = gmZ m N u := by
    rw [gmD, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]
  have hcz : ∑ i, gmCoeff m N i * gmZ m N u i = ∑ i, gmRhs m N i * gmD m N u i := by
    rw [← hGd, dotProduct_gmGram_mulVec_comm, gmGram_mulVec_gmCoeff h]
  have hbd : ∑ i, gmRhs m N i * gmD m N u i = ∑ i, gmTarget m N i * gmD m N u i -
      ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) * gmQ m N u ((k : ℝ) / N) := by
    simp only [gmRhs, gmQ, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by
      rw [gmVec]; ring
  rw [hhead, htail, hcz, hbd, gmPsi]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-! ### The real analytic kernel -/

/-- The real Bose kernel with its analytic value `1/2` at `0`. -/
def boseKernelR (t : ℝ) : ℝ := (boseKernelE (t : ℂ)).re

theorem ofReal_mem_boseStrip (t : ℝ) : (t : ℂ) ∈ boseStrip := by
  rw [mem_boseStrip, Complex.ofReal_im, abs_zero]; positivity

theorem boseKernelR_of_pos {t : ℝ} (ht : 0 < t) : boseKernelR t = fusionBoseDefect t := by
  rw [boseKernelR, boseKernelE_ofReal ht, Complex.ofReal_re]

theorem hasDerivAt_boseKernelR (t : ℝ) :
    HasDerivAt boseKernelR (deriv boseKernelE (t : ℂ)).re t :=
  ((boseKernelE_differentiableOn.differentiableAt
    (isOpen_boseStrip.mem_nhds (ofReal_mem_boseStrip t))).hasDerivAt).real_of_complex

theorem continuous_deriv_boseKernelR : Continuous fun t : ℝ => (deriv boseKernelE (t : ℂ)).re :=
  Complex.continuous_re.comp ((boseKernelE_analyticOnNhd.deriv.continuousOn).comp_continuous
    Complex.continuous_ofReal ofReal_mem_boseStrip)

theorem continuous_boseKernelR : Continuous boseKernelR :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_boseKernelR t).continuousAt

/-! ### Identity (E) -/

theorem gmExp_succ_nonneg (m : ℕ) (j : Fin (m + 1)) : 0 ≤ gmExp m j.succ := by
  unfold gmExp
  rw [Fin.val_succ, if_neg (Nat.succ_ne_zero _)]
  split_ifs <;> omega

/-- The regular kernel `Φ_N(u, x) = h(ux) - d_0(u) - Σ_j d_j(u) x^{2j-1}` (the `x⁻¹` channel
removed). -/
def gmPhi (m N : ℕ) (u x : ℝ) : ℝ :=
  boseKernelR (u * x) - ∑ j : Fin (m + 1), gmD m N u j.succ * x ^ (gmExp m j.succ).toNat

/-- Its `x`-derivative. -/
def gmPhiDeriv (m N : ℕ) (u x : ℝ) : ℝ :=
  u * (deriv boseKernelE ((u * x : ℝ) : ℂ)).re -
    ∑ j : Fin (m + 1), gmD m N u j.succ *
      ((gmExp m j.succ).toNat * x ^ ((gmExp m j.succ).toNat - 1))

theorem hasDerivAt_gmPhi (m N : ℕ) (u x : ℝ) :
    HasDerivAt (gmPhi m N u) (gmPhiDeriv m N u x) x := by
  have h1 : HasDerivAt (fun x => boseKernelR (u * x)) ((deriv boseKernelE ((u * x : ℝ) : ℂ)).re * u) x :=
    (hasDerivAt_boseKernelR (u * x)).comp x ((hasDerivAt_id x).const_mul u |>.congr_deriv (by ring))
  have h2 : HasDerivAt (fun x : ℝ => ∑ j : Fin (m + 1), gmD m N u j.succ * x ^ (gmExp m j.succ).toNat)
      (∑ j : Fin (m + 1), gmD m N u j.succ *
        ((gmExp m j.succ).toNat * x ^ ((gmExp m j.succ).toNat - 1))) x := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact (hasDerivAt_pow _ x).const_mul _
  have := h1.sub h2
  rw [gmPhiDeriv, mul_comm u]
  exact this

theorem continuous_gmPhiDeriv (m N : ℕ) (u : ℝ) : Continuous (gmPhiDeriv m N u) := by
  unfold gmPhiDeriv
  refine Continuous.sub (continuous_const.mul ?_) (by fun_prop)
  exact continuous_deriv_boseKernelR.comp (continuous_const.mul continuous_id)

/-- The Mertens function `A(y) = Σ_{k ≤ y} μ(k)`. -/
def mertensFloor (y : ℝ) : ℝ := ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, ((μ k : ℤ) : ℝ)

/-- `h(ux) - q_N(u, x) = Φ_N(u, x) - d_{-1}(u)/x` for `x > 0`. -/
theorem sub_gmQ_eq {m N : ℕ} {u x : ℝ} (hux : 0 < u * x) :
    fusionBoseDefect (u * x) - gmQ m N u x = gmPhi m N u x - gmD m N u 0 / x := by
  rw [gmQ, gmPhi, boseKernelR_of_pos hux, Fin.sum_univ_succ]
  have hsucc : ∀ j : Fin (m + 1), x ^ gmExp m j.succ * gmD m N u j.succ =
      gmD m N u j.succ * x ^ (gmExp m j.succ).toNat := fun j => by
    rw [← zpow_natCast, Int.toNat_of_nonneg (gmExp_succ_nonneg m j), mul_comm]
  simp only [hsucc]
  have h0 : gmExp m 0 = -1 := gmExp_zero m
  rw [h0, zpow_neg_one]
  ring

/-- **The Abel decomposition (E).** -/
theorem heatError_gmRow_abel {m N : ℕ} (hN : 0 < N) (h : IsUnit (gmGram m N).det) {u : ℝ}
    (hu : 0 < u) :
    chronologicalHeatError (gmRow m N) N (u / N) =
      gmPsi m N u - N * (∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) / k) * gmD m N u 0 +
        mertensFloor (N / 2 : ℕ) * gmPhi m N u ((N / 2 : ℕ) / N) -
        ∫ x in (0 : ℝ)..((N / 2 : ℕ) / N), mertensFloor (N * x) * gmPhiDeriv m N u x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set M := N / 2 with hM
  rw [heatError_gmRow_signed h]
  -- split off the harmonic channel
  have hsplit : ∑ k ∈ Finset.Ioc 0 M, ((μ k : ℤ) : ℝ) *
      (fusionBoseDefect (u * ((k : ℝ) / N)) - gmQ m N u ((k : ℝ) / N)) =
      ∑ k ∈ Finset.Ioc 0 M, ((μ k : ℤ) : ℝ) * gmPhi m N u ((k : ℝ) / N) -
        N * (∑ k ∈ Finset.Ioc 0 M, ((μ k : ℤ) : ℝ) / k) * gmD m N u 0 := by
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    rw [sub_gmQ_eq (by positivity)]
    field_simp
  -- Abel summation for the regular kernel
  set f : ℝ → ℝ := fun y => gmPhi m N u (y / N) with hf
  have hfd : ∀ y, HasDerivAt f (gmPhiDeriv m N u (y / N) * (1 / N)) y := fun y => by
    have h := (hasDerivAt_gmPhi m N u (y / N)).comp y ((hasDerivAt_id y).div_const (N : ℝ))
    simpa [hf, Function.comp_def] using h
  have hderiv : deriv f = fun y => gmPhiDeriv m N u (y / N) * (1 / N) :=
    funext fun y => (hfd y).deriv
  have habel := sum_mul_eq_sub_integral_mul' (c := fun k => ((μ k : ℤ) : ℝ)) (f := f) M
    (fun t _ => (hfd t).differentiableAt)
    (by
      rw [hderiv]
      exact ((continuous_gmPhiDeriv m N u).comp (continuous_id.div_const _)).mul
        continuous_const |>.continuousOn.integrableOn_Icc)
  have hIcc : ∀ g : ℕ → ℝ, g 0 = 0 → ∑ k ∈ Finset.Icc 0 M, g k = ∑ k ∈ Finset.Ioc 0 M, g k := by
    intro g hg0
    rw [← Finset.sum_subset (s₁ := Finset.Ioc 0 M) (s₂ := Finset.Icc 0 M)
      (fun k hk => Finset.mem_Icc.mpr ⟨Nat.zero_le k, (Finset.mem_Ioc.mp hk).2⟩)
      (fun k hk hk' => by
        have : k = 0 := by
          by_contra h0
          exact hk' (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, (Finset.mem_Icc.mp hk).2⟩)
        subst this; exact hg0)]
  rw [hIcc _ (by simp), hderiv] at habel
  have hlhs : ∑ k ∈ Finset.Ioc 0 M, f k * ((μ k : ℤ) : ℝ) =
      ∑ k ∈ Finset.Ioc 0 M, ((μ k : ℤ) : ℝ) * gmPhi m N u ((k : ℝ) / N) :=
    Finset.sum_congr rfl fun k _ => by rw [hf]; ring
  have hmert : ∑ k ∈ Finset.Icc 0 M, ((μ k : ℤ) : ℝ) = mertensFloor M := by
    rw [mertensFloor, Nat.floor_natCast]
  -- the substitution `y = N x`
  have hsub : ∫ t in Set.Ioc (0 : ℝ) M, gmPhiDeriv m N u (t / N) * (1 / N) *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((μ k : ℤ) : ℝ) =
      ∫ x in (0 : ℝ)..((M : ℝ) / N), mertensFloor (N * x) * gmPhiDeriv m N u x := by
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg M)]
    have hG : ∀ t : ℝ, gmPhiDeriv m N u (t / N) * (1 / N) *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, ((μ k : ℤ) : ℝ) =
        (1 / N) * ((fun x => mertensFloor (N * x) * gmPhiDeriv m N u x) (t / N)) := by
      intro t
      simp only [mertensFloor]
      rw [mul_div_cancel₀ t hNr.ne']
      ring
    simp only [hG]
    have hcd := intervalIntegral.integral_comp_div (a := 0) (b := (M : ℝ))
      (fun x => mertensFloor (N * x) * gmPhiDeriv m N u x) hNr.ne'
    rw [intervalIntegral.integral_const_mul, hcd, zero_div, smul_eq_mul, ← mul_assoc,
      one_div_mul_cancel hNr.ne', one_mul]
  rw [hlhs, hmert, hsub] at habel
  rw [hsplit, habel, hf]
  ring

/-! ### Square integrability of the terms of (E) on `[0, log N]` -/

theorem memLp_Icc_of_measurable_bound {L : ℝ} {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ u ∈ Icc 0 L, |f u| ≤ C) : MemLp f 2 (volume.restrict (Icc 0 L)) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) L)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Icc]; simp)
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  exact Eventually.of_forall fun u hu => by rw [Real.norm_eq_abs]; exact hC u hu

theorem measurable_gmZ (m N : ℕ) (i : Fin (m + 2)) : Measurable fun u => gmZ m N u i := by
  have hb := measurable_fusionBoseDefect
  unfold gmZ
  fun_prop

theorem measurable_gmD (m N : ℕ) (i : Fin (m + 2)) : Measurable fun u => gmD m N u i := by
  unfold gmD Matrix.mulVec dotProduct
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_gmZ m N j)

theorem abs_gmZ_le (m N : ℕ) (u : ℝ) (i : Fin (m + 2)) : |gmZ m N u i| ≤ 2 * N := by
  unfold gmZ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.Ioc (N / 2) N, |gmVec m N k i * fusionBoseDefect (u * ((k : ℝ) / N))|
      ≤ ∑ _k ∈ Finset.Ioc (N / 2) N, (2 : ℝ) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hb := fusionBoseDefect_bounds (u * ((k : ℝ) / N))
        rw [abs_mul, abs_of_nonneg hb.1]
        exact (mul_le_mul (abs_gmVec_le hk i) hb.2.1 hb.1 zero_le_two).trans_eq (mul_one 2)
    _ ≤ 2 * N := by
        rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_comm]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sub_le N (N / 2)) zero_le_two

/-- A uniform bound for the projection coefficients. -/
theorem exists_abs_gmD_le (m N : ℕ) : ∃ C : ℝ, ∀ u i, |gmD m N u i| ≤ C := by
  refine ⟨∑ i, ∑ j, |(gmGram m N)⁻¹ i j| * (2 * N), fun u i => ?_⟩
  unfold gmD Matrix.mulVec dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |(gmGram m N)⁻¹ i j * gmZ m N u j| ≤ ∑ j, |(gmGram m N)⁻¹ i j| * (2 * N) :=
        Finset.sum_le_sum fun j _ => by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_gmZ_le m N u j) (abs_nonneg _)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ j, |(gmGram m N)⁻¹ i j| * (2 * N))
        (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)

theorem abs_boseKernelR_le {t : ℝ} (ht : 0 ≤ t) : |boseKernelR t| ≤ 1 := by
  rcases ht.eq_or_lt with rfl | hpos
  · rw [boseKernelR, Complex.ofReal_zero, boseKernelE_zero]; norm_num
  · rw [boseKernelR_of_pos hpos, abs_of_nonneg (fusionBoseDefect_bounds t).1]
    exact (fusionBoseDefect_bounds t).2.1

theorem measurable_heatError (a : ℕ → ℝ) (N : ℕ) : Measurable (chronologicalHeatError a N) := by
  have hb := measurable_fusionBoseDefect
  unfold chronologicalHeatError
  fun_prop

/-- **Every term of the Abel decomposition is square integrable on `[0, log N]`.** -/
theorem abel_terms_memLp {m N : ℕ} (hN : 0 < N) (h : IsUnit (gmGram m N).det) :
    MemLp (gmPsi m N) 2 (volume.restrict (Icc 0 (Real.log N))) ∧
      MemLp (fun u => gmD m N u 0) 2 (volume.restrict (Icc 0 (Real.log N))) ∧
      MemLp (fun u => gmPhi m N u ((N / 2 : ℕ) / N)) 2 (volume.restrict (Icc 0 (Real.log N))) ∧
      MemLp (fun u => ∫ x in (0 : ℝ)..((N / 2 : ℕ) / N),
        mertensFloor (N * x) * gmPhiDeriv m N u x) 2 (volume.restrict (Icc 0 (Real.log N))) ∧
      MemLp (fun u => chronologicalHeatError (gmRow m N) N (u / N)) 2
        (volume.restrict (Icc 0 (Real.log N))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨CD, hCD⟩ := exists_abs_gmD_le m N
  set θ : ℝ := (N / 2 : ℕ) / N with hθ
  have hθ0 : 0 ≤ θ := by positivity
  -- the target part
  have hPsi : MemLp (gmPsi m N) 2 (volume.restrict (Icc 0 (Real.log N))) := by
    refine memLp_Icc_of_measurable_bound (C := 1 + ∑ i, |gmTarget m N i| * CD) ?_ fun u hu => ?_
    · unfold gmPsi
      exact (Real.measurable_exp.comp (measurable_id.div_const _).neg).add
        (Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_gmD m N i))
    · unfold gmPsi
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hu.1 hNr.le))
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hCD u i) (abs_nonneg _)
  have hD : MemLp (fun u => gmD m N u 0) 2 (volume.restrict (Icc 0 (Real.log N))) :=
    memLp_Icc_of_measurable_bound (measurable_gmD m N 0) fun u _ => hCD u 0
  have hPhi : MemLp (fun u => gmPhi m N u θ) 2 (volume.restrict (Icc 0 (Real.log N))) := by
    refine memLp_Icc_of_measurable_bound
      (C := 1 + ∑ j : Fin (m + 1), CD * |θ ^ (gmExp m j.succ).toNat|) ?_ fun u hu => ?_
    · unfold gmPhi
      exact (continuous_boseKernelR.measurable.comp (measurable_id.mul_const _)).sub
        (Finset.measurable_sum _ fun j _ => (measurable_gmD m N _).mul measurable_const)
    · unfold gmPhi
      refine (abs_sub _ _).trans (add_le_add (abs_boseKernelR_le (mul_nonneg hu.1 hθ0)) ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hCD u _) (abs_nonneg _)
  have hr : MemLp (fun u => chronologicalHeatError (gmRow m N) N (u / N)) 2
      (volume.restrict (Icc 0 (Real.log N))) := by
    refine memLp_Icc_of_measurable_bound
      (C := 1 + ∑ k ∈ Finset.Ioc 0 N, |gmRow m N k|) ?_ fun u hu => ?_
    · exact (measurable_heatError _ N).comp (measurable_id.div_const _)
    · have ht : 0 ≤ u / N := div_nonneg hu.1 hNr.le
      unfold chronologicalHeatError
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        have hb := fusionBoseDefect_bounds ((k : ℝ) * (u / N))
        rw [abs_mul, abs_of_nonneg hb.1]
        exact mul_le_of_le_one_right (abs_nonneg _) hb.2.1
  refine ⟨hPsi, hD, hPhi, ?_, hr⟩
  -- the Abel integral is a combination of the other terms off `u = 0`
  have hcomb : MemLp (fun u => gmPsi m N u -
      N * (∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) / k) * gmD m N u 0 +
      mertensFloor (N / 2 : ℕ) * gmPhi m N u θ -
      chronologicalHeatError (gmRow m N) N (u / N)) 2 (volume.restrict (Icc 0 (Real.log N))) :=
    ((hPsi.sub (hD.const_mul _)).add (hPhi.const_mul _)).sub hr
  refine hcomb.ae_eq ?_
  have hnull : ∀ᵐ u ∂(volume.restrict (Icc (0 : ℝ) (Real.log N))), u ≠ 0 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
      refine ae_iff.mpr ?_
      simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
      exact measure_singleton 0
    exact this.mono fun u hu _ => hu
  filter_upwards [hnull, ae_restrict_mem measurableSet_Icc] with u hu0 hu
  have hu : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  rw [heatError_gmRow_abel hN h hu]
  ring

/-- **The cost of the normalized harmonic channel.**  On the logarithmic window the normalized
`L²` norm of the harmonic term `N H_M d_{-1}` equals `√N |H_M| ‖d_{-1}‖_{L²([0, log N])}`. -/
theorem harmonic_channel_norm (m N : ℕ) (hN : 0 < N) :
    Real.sqrt ((N : ℝ)⁻¹ * ∫ u in (0 : ℝ)..Real.log N,
      (N * (∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) / k) * gmD m N u 0) ^ 2) =
      Real.sqrt N * |∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) / k| *
        Real.sqrt (∫ u in (0 : ℝ)..Real.log N, gmD m N u 0 ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set H := ∑ k ∈ Finset.Ioc 0 (N / 2), ((μ k : ℤ) : ℝ) / k
  have hrw : ∀ u : ℝ, (N * H * gmD m N u 0) ^ 2 = (N * H) ^ 2 * gmD m N u 0 ^ 2 := fun u => by ring
  simp only [hrw, intervalIntegral.integral_const_mul]
  rw [← mul_assoc, show (N : ℝ)⁻¹ * (N * H) ^ 2 = N * H ^ 2 by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq_eq_abs]

end RHTower
