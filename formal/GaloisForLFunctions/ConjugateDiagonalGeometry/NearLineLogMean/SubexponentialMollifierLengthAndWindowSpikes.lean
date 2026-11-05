import GaloisForLFunctions.ArithmeticProduction.LongMollifiersImplyCriticalClustering
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TwoSidedThetaMollifierTrap
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount

/-!
# Complex Necessary-Length Law up to `exp(T^{1/60})`, Exact `exp(c log²T)` Rate Threshold, and Multi-Window Critical-Line Spikes

This module establishes three unconditional bridges across the near-line mollifier hierarchy:

1. **Hermitian analytic trace and unconditional removal of real-coefficient assumptions (`hbr`):**
   Replacing `(Ψ(z + iT) + Ψ(z - iT)) / 2` by the Hermitian analytic trace
   `edPolyHermitianTrace a s T z = (Ψ(z + iT) + Ψ*(z - iT)) / 2`, where `Ψ*(w) = ∑_{n ∈ s} conj(a_n) n^{-w}`,
   recovers `edPolyHermitianTrace a s T x = Re Ψ(x + iT)` identically for all complex coefficients
   `a : ℕ → ℂ` and preserves both the `5 / 16` head-dominance bound at `z = 4` and the half-plane
   `ℓ¹` bound. Consequently, Backlund's horizontal-edge bound, the Levinson Littlewood budget,
   the critical-line log-integral ceiling, the implications `ComplexMollifiedSecondMomentLaw → CriticalClustering`
   and `ComplexSecondMomentRate K₀ → LogFreeNearLineZeroDensity ∧ LogFreeNearLineWindowOccupancy`,
   and the left-of-line second-moment floor hold unconditionally for all complex Dirichlet polynomials.

2. **Uniform stretched-exponential necessary-length law and exact `exp(c log²T)` rate threshold:**
   Eventually as `T → ∞`, simultaneously for all `1 ≤ N` with `log N ≤ T^{1/60}` and all complex
   Dirichlet polynomials `M(s) = ∑_{n=1}^N b_n n^{-s}` (`b 1 = 1`, `‖b n‖ ≤ 1`),
   `∫_T^{2T} ‖ζ(1/2 + it) M(1/2 + it)‖² dt ≥ (1 + log T / (8 log T + 6 log N)) T`.
   In particular, achieving the `D_zero`/`D_win`-forcing excess `K₀ / log T` requires
   `log N(T) ≥ (log T)² / (6 K₀) - (4 / 3) log T` eventually, ruling out all polynomial and all
   sub-threshold `exp(δ (log T)²)` (`δ < 1 / (6 K₀)`) complex mollifier families, while any complex
   mollifier family with normalized second moment tending to `1` forces `log N(T) / log T → +∞`.

3. **Superposed multi-window critical-line zero spikes (`D_win`):**
   Coloring occupied Burnol unit windows `m ∈ [⌈V⌉, ⌊2V⌋]` modulo `⌈2R + 7⌉₊` superposes
   `TwoSidedThetaMollifierTrap`'s localized critical-line zero spikes across pairwise disjoint
   ordinate intervals, forcing a lower bound `(S.card / ⌈2R + 7⌉₊) · (3 δ / 4) e^{-α/2} Y^{2δ}`
   (and `(S.card / ⌈2R + 7⌉₊) · (3 δ / 4) e^{-2αδ²} Y^{2δ}` whenever `α ≤ log Y`) on the
   critical-line second moment over `[V - R - 3, 2V + R + 3]`.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Metric MeromorphicOn intervalIntegral Topology
open scoped BigOperators Interval Classical

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

open _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticProduction
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogScaleHeckeDefect
open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1. Hermitian analytic trace and complex-coefficient Littlewood / clustering / rate theorems -/

/-- Exact conjugation law for finite complex Dirichlet polynomials:
`conj(∑_{n ∈ s} a_n n^{-z}) = ∑_{n ∈ s} conj(a_n) n^{-conj(z)}`. -/
theorem edPoly_conj_star (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (z : ℂ) :
    (starRingEnd ℂ) (edPoly a s z) =
      edPoly (fun n => (starRingEnd ℂ) (a n)) s ((starRingEnd ℂ) z) := by
  unfold edPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hs n hn
  have hne : (((n : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hpos)
  have hlog : Complex.log ((n : ℝ) : ℂ) = ((Real.log n : ℝ) : ℂ) :=
    (Complex.ofReal_log hpos.le).symm
  rw [map_mul, Complex.cpow_def_of_ne_zero hne, Complex.cpow_def_of_ne_zero hne,
    hlog, ← Complex.exp_conj]
  congr 2
  rw [map_mul, Complex.conj_ofReal, map_neg]

/-- The Hermitian analytic trace `(Ψ(z + iT) + Ψ*(z - iT)) / 2` of a complex Dirichlet polynomial
at height `T`, extending `x ↦ Re Ψ(x + iT)` holomorphically to all `z ∈ ℂ`. -/
def edPolyHermitianTrace (a : ℕ → ℂ) (s : Finset ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  (edPoly a s (z + (T : ℂ) * I) +
    edPoly (fun n => (starRingEnd ℂ) (a n)) s (z - (T : ℂ) * I)) / 2

theorem differentiable_edPolyHermitianTrace (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) :
    Differentiable ℂ (edPolyHermitianTrace a s T) := by
  have hd1 := differentiable_edPoly a hs
  have hd2 := differentiable_edPoly (fun n => (starRingEnd ℂ) (a n)) hs
  exact fun z => (((hd1 _).comp z (differentiableAt_id.add_const _)).add
    ((hd2 _).comp z (differentiableAt_id.sub_const _))).div_const 2

theorem analyticOnNhd_edPolyHermitianTrace (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) (K : Set ℂ) :
    AnalyticOnNhd ℂ (edPolyHermitianTrace a s T) K :=
  fun z _ => (analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_edPolyHermitianTrace a hs T)) z (Set.mem_univ z)

/-- On the real axis `z = x ∈ ℝ`, `edPolyHermitianTrace a s T x = Re Ψ(x + iT)` identically for all
complex coefficient sequences `a : ℕ → ℂ`. -/
theorem edPolyHermitianTrace_ofReal (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (T x : ℝ) :
    edPolyHermitianTrace a s T (x : ℂ) =
      (((edPoly a s ((x : ℂ) + (T : ℂ) * I)).re : ℝ) : ℂ) := by
  have hconj : ((x : ℂ) - (T : ℂ) * I) = (starRingEnd ℂ) ((x : ℂ) + (T : ℂ) * I) := by
    simp [Complex.ext_iff]
  rw [edPolyHermitianTrace, hconj, ← edPoly_conj_star a hs, Complex.add_conj]
  push_cast
  ring

/-- Uniform half-plane `ℓ¹` bound on `Re z ≥ x` for the Hermitian analytic trace. -/
theorem norm_edPolyHermitianTrace_le_of_re_ge (a : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ) {x : ℝ} {z : ℂ} (hz : x ≤ z.re) :
    ‖edPolyHermitianTrace a s T z‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) := by
  have hkey : ∀ (c : ℕ → ℂ) (w : ℂ), (∀ n ∈ s, ‖c n‖ = ‖a n‖) → w.re = z.re →
      ‖edPoly c s w‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) := by
    intro c w hnorm hw
    refine (norm_edPoly_le c hs w).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [hnorm n hn]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs n hn
    have hmono : ((n : ℝ) ^ (-w.re)) ≤ ((n : ℝ) ^ (-x)) := by
      refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
      rw [hw]; linarith
    exact mul_le_mul_of_nonneg_left hmono (norm_nonneg _)
  have h1 : ‖edPoly a s (z + (T : ℂ) * I)‖ ≤ ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) :=
    hkey a _ (fun _ _ => rfl) (by simp)
  have h2 : ‖edPoly (fun n => (starRingEnd ℂ) (a n)) s (z - (T : ℂ) * I)‖ ≤
      ∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (-x)) :=
    hkey _ _ (fun n _ => Complex.norm_conj (a n)) (by simp)
  rw [edPolyHermitianTrace, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
  have htri := norm_add_le (edPoly a s (z + (T : ℂ) * I))
    (edPoly (fun n => (starRingEnd ℂ) (a n)) s (z - (T : ℂ) * I))
  linarith [htri, h1, h2]

/-- Head dominance at `z = 4` for the Hermitian analytic trace of any normalized bounded complex
Dirichlet polynomial (`b 1 = 1`, `‖b n‖ ≤ 1`). -/
theorem five_sixteenth_le_norm_edPolyHermitianTrace_four (b : ℕ → ℂ) {s : Finset ℕ}
    (hs : ∀ n ∈ s, 1 ≤ n) (h1 : 1 ∈ s) (hb1 : b 1 = 1) (hbn : ∀ n ∈ s, ‖b n‖ ≤ 1) (T : ℝ) :
    (5 / 16 : ℝ) ≤ ‖edPolyHermitianTrace b s T 4‖ := by
  have hexp4 : Real.exp (-(Real.log 2) * (4 : ℝ)) = 1 / 16 := by
    rw [exp_neg_log_two_eq, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hp : ‖edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1‖ ≤ 11 / 16 := by
    have h := norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn
      (z := (4 : ℂ) + (T : ℂ) * I) (by simp; norm_num)
    have hre : ((4 : ℂ) + (T : ℂ) * I).re = 4 := by simp
    rw [hre, hexp4] at h; linarith
  have hb1_conj : (starRingEnd ℂ) (b 1) = 1 := by rw [hb1, map_one]
  have hbn_conj : ∀ n ∈ s, ‖(starRingEnd ℂ) (b n)‖ ≤ 1 := fun n hn => by
    rw [Complex.norm_conj]; exact hbn n hn
  have hm : ‖edPoly (fun n => (starRingEnd ℂ) (b n)) s ((4 : ℂ) - (T : ℂ) * I) - 1‖ ≤ 11 / 16 := by
    have h := norm_edPoly_sub_one_le_exp (fun n => (starRingEnd ℂ) (b n)) hs h1 hb1_conj hbn_conj
      (z := (4 : ℂ) - (T : ℂ) * I) (by simp; norm_num)
    have hre : ((4 : ℂ) - (T : ℂ) * I).re = 4 := by simp
    rw [hre, hexp4] at h; linarith
  have htr : edPolyHermitianTrace b s T 4 - 1 =
      ((edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1) +
        (edPoly (fun n => (starRingEnd ℂ) (b n)) s ((4 : ℂ) - (T : ℂ) * I) - 1)) / 2 := by
    unfold edPolyHermitianTrace; ring
  have hdist : ‖edPolyHermitianTrace b s T 4 - 1‖ ≤ 11 / 16 := by
    rw [htr, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have htri := norm_add_le (edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1)
      (edPoly (fun n => (starRingEnd ℂ) (b n)) s ((4 : ℂ) - (T : ℂ) * I) - 1)
    linarith [htri, hp, hm]
  have hrev := norm_sub_norm_le (1 : ℂ) (edPolyHermitianTrace b s T 4)
  rw [norm_one, norm_sub_rev] at hrev
  linarith

/-- Jensen's disc divisor bound on `closedBall 4 |r|` (`0 < r < 8`) for `edPolyHermitianTrace`. -/
theorem edPolyHermitianTrace_count_le (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    {r m Mb : ℝ} (hr : 0 < r) (hrlt : r < 8) (hm : 0 < m) (hM1 : 1 ≤ Mb)
    (hcentre : m ≤ ‖edPolyHermitianTrace a s T 4‖)
    (hmass : (∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb) :
    ∑ᶠ u, MeromorphicOn.divisor (edPolyHermitianTrace a s T) (closedBall (4 : ℂ) |r|) u
      ≤ Real.log (Mb / m) / Real.log (8 / r) := by
  have hsphere : ∀ z ∈ sphere (4 : ℂ) |(8 : ℝ)|, ‖edPolyHermitianTrace a s T z‖ ≤ Mb := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num : (0 : ℝ) < 8)] at hz
    have hre : (-4 : ℝ) ≤ z.re := by
      have h := Complex.abs_re_le_norm (z - 4)
      have hrz : (z - 4).re = z.re - 4 := by simp
      rw [hrz, hz, abs_le] at h
      linarith [h.1]
    refine (norm_edPolyHermitianTrace_le_of_re_ge a hs T hre).trans (le_trans ?_ hmass)
    exact le_of_eq (Finset.sum_congr rfl fun _ _ => by norm_num)
  exact sum_divisor_le_of_bounds (c := (4 : ℂ)) (r := r) (R := (8 : ℝ))
    (M := Mb) (m := m) (f := edPolyHermitianTrace a s T)
    (by rwa [abs_of_pos hr])
    (by rw [abs_of_pos hr, abs_of_pos (by norm_num : (0 : ℝ) < 8)]; exact hrlt)
    hM1 hm (analyticOnNhd_edPolyHermitianTrace a hs T _) hcentre hsphere

/-- **Backlund weighted horizontal-edge bound for arbitrary complex Dirichlet polynomials.** -/
theorem abs_integral_weighted_im_logDeriv_edPoly_complex_le
    (a : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n) (T : ℝ)
    {c e r m Mb : ℝ} (hce : c < e) (hr : 0 < r) (hrlt : r < 8)
    (hcr : 4 - r ≤ c) (her : e ≤ 4 + r)
    (hne : ∀ x ∈ Set.Icc c e, edPoly a s ((x : ℂ) + (T : ℂ) * I) ≠ 0)
    (hm : 0 < m) (hM1 : 1 ≤ Mb)
    (hcentre : m ≤ ‖edPolyHermitianTrace a s T 4‖)
    (hmass : (∑ n ∈ s, ‖a n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb) :
    |∫ x in c..e, (x - c) *
        (logDeriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ 2 * (e - c) *
        ((Real.log (Mb / m) / Real.log (8 / r) + 1) * Real.pi) := by
  classical
  set K : Set ℂ := closedBall (4 : ℂ) |r| with hK
  have hKcompact : IsCompact K := isCompact_closedBall _ _
  have hana : AnalyticOnNhd ℂ (edPolyHermitianTrace a s T) K :=
    analyticOnNhd_edPolyHermitianTrace a hs T K
  have htracene : ∃ z : ℂ, edPolyHermitianTrace a s T z ≠ 0 := by
    refine ⟨4, fun h0 => ?_⟩
    rw [h0, norm_zero] at hcentre; linarith
  have hord : ∀ z ∈ K, analyticOrderAt (edPolyHermitianTrace a s T) z ≠ ⊤ := fun z _ =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero
      (analyticOnNhd_edPolyHermitianTrace a hs T Set.univ) htracene z
  have hfin : {u : ℂ | u ∈ K ∧ edPolyHermitianTrace a s T u = 0}.Finite := by
    refine ((MeromorphicOn.divisor (edPolyHermitianTrace a s T) K).finiteSupport hKcompact).subset ?_
    intro u hu
    rw [Function.mem_support]
    have h1 := one_le_divisor_of_zero hana hu.1 hu.2 (hord u hu.1)
    omega
  have hfinR : {x : ℝ | (x : ℂ) ∈ K ∧ edPolyHermitianTrace a s T (x : ℂ) = 0}.Finite := by
    refine Set.Finite.ofFinset (hfin.toFinset.preimage (fun x : ℝ => (x : ℂ))
      (fun _ _ _ _ h => Complex.ofReal_inj.mp h)) ?_
    intro x; rw [Finset.mem_preimage, Set.Finite.mem_toFinset]; rfl
  set Z : Finset ℝ := hfinR.toFinset with hZdef
  set f : ℝ → ℂ := fun x => edPoly a s ((x : ℂ) + (T : ℂ) * I) with hfdef
  set f' : ℝ → ℂ := fun x => deriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I) with hf'def
  have hZmem : ∀ x ∈ Set.Ioo c e, (f x).re = 0 → x ∈ Z := by
    intro x hx hzero
    rw [hZdef, Set.Finite.mem_toFinset]
    refine ⟨?_, ?_⟩
    · rw [hK, mem_closedBall, abs_of_pos hr, Complex.dist_eq]
      have hval : ‖((x : ℂ) - 4)‖ = |x - 4| := by
        rw [show ((x : ℂ) - 4) = ((x - 4 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hval, abs_le]; constructor <;> linarith [hx.1, hx.2]
    · rw [edPolyHermitianTrace_ofReal a hs T x]
      rw [hfdef] at hzero; simp only at hzero; rw [hzero]; norm_num
  have hbound := abs_integral_weighted_im_logDeriv_le_of_finite_re_zeros hce.le
    (f := f) (f' := f') (fun x => hasDerivAt_edPoly_horiz a hs T x)
    (continuous_edPoly_horiz a hs T) (continuous_deriv_edPoly_horiz a hs T)
    (fun x hx => hne x hx) Z hZmem
  have hcongr : ∀ x ∈ Set.uIcc c e,
      (x - c) * (f' x / f x).im =
        (x - c) * (logDeriv (edPoly a s) ((x : ℂ) + (T : ℂ) * I)).im := by
    intro x _; rw [hf'def, hfdef, logDeriv_apply]
  rw [intervalIntegral.integral_congr hcongr] at hbound
  refine hbound.trans ?_
  have hcard : ((Z.filter (fun z => z ∈ Set.Ioo c e)).card : ℝ)
      ≤ Real.log (Mb / m) / Real.log (8 / r) := by
    have hsubc : (Z.filter (fun z => z ∈ Set.Ioo c e)).card ≤ Z.card := Finset.card_filter_le _ _
    have himg : (Z.image (fun x : ℝ => (x : ℂ))).card = Z.card :=
      Finset.card_image_of_injective _ (fun _ _ h => Complex.ofReal_inj.mp h)
    have hS : ∀ z ∈ Z.image (fun x : ℝ => (x : ℂ)),
        z ∈ K ∧ edPolyHermitianTrace a s T z = 0 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      rwa [hZdef, Set.Finite.mem_toFinset] at hx
    have hle := card_le_divisor_sum hKcompact hana hord _ hS
    rw [himg] at hle
    have hjensen := edPolyHermitianTrace_count_le a hs T hr hrlt hm hM1 hcentre hmass
    have hcast : ((Z.card : ℤ) : ℝ)
        ≤ ((∑ᶠ u, MeromorphicOn.divisor (edPolyHermitianTrace a s T) K u : ℤ) : ℝ) := by
      exact_mod_cast hle
    have hsubcast : ((Z.filter (fun z => z ∈ Set.Ioo c e)).card : ℝ) ≤ (Z.card : ℝ) := by
      exact_mod_cast hsubc
    push_cast at hcast; linarith
  have hstep : (((Z.filter (fun z => z ∈ Set.Ioo c e)).card : ℝ) + 1) * Real.pi
      ≤ (Real.log (Mb / m) / Real.log (8 / r) + 1) * Real.pi :=
    mul_le_mul_of_nonneg_right (by linarith [hcard]) Real.pi_pos.le
  have hwidth : (0 : ℝ) < e - c := by linarith
  nlinarith [hstep, hwidth]

/-- **Littlewood's floor for any normalized bounded complex Dirichlet polynomial on `Re s = 1/2`.** -/
theorem exists_edPoly_line_logMean_floor_complex :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ : ℝ, T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        -(C + K * Real.log Mb) ≤
          ∫ t in T₁..T₂,
            Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  classical
  set α : ℝ := Real.log 2
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 11 * Real.exp (-α * (15 / 2)) / α)
  set Cfar' : ℝ := 2 * ((2 * 11 * Real.exp α) * Real.exp (-α * (15 / 2)) / α)
  set L : ℝ := Real.log (32 / 15)
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  set KH : ℝ := 2 * 7 * Real.pi
  have hKHpos : 0 < KH := by positivity
  refine ⟨Cfar + 7 * Cfar' + 2 * (KH * (Real.log (16 / 5) / L + 1)), 2 * (KH / L),
    by positivity, by positivity, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ hT hP1 hP2
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  set Ψ : ℂ → ℂ := edPoly b s
  have hΨan : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have huIccx : uIcc (1 / 2 : ℝ) (15 / 2 : ℝ) = Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) :=
    uIcc_of_le (by norm_num)
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re → AnalyticAt ℂ Ψ z := fun z _ => hΨan z (Set.mem_univ z)
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re → ‖Ψ z - 1‖ ≤ 11 * Real.exp (-α * z.re) :=
    fun z hz => norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn (z := z) (by linarith)
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re → ‖Ψ z - 1‖ ≤ 1 / 2 :=
    fun z hz => norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn hz.le
  have hfarlog : |∫ t in T₁..T₂, Real.log ‖Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂, (logDeriv Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    have h := hfarsmall (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
    rw [h0, show ‖(0 : ℂ) - 1‖ = 1 by simp] at h
    norm_num at h
  have hhoriz : ∀ T : ℝ,
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), Ψ ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..(15 / 2 : ℝ), (x - 1 / 2) *
          (logDeriv Ψ ((x : ℂ) + (T : ℂ) * I)).im| ≤
        KH * (Real.log (16 / 5) / L + 1) + (KH / L) * Real.log Mb := by
    intro T hne
    have h := abs_integral_weighted_im_logDeriv_edPoly_complex_le b hs T
      (c := 1 / 2) (e := 15 / 2) (r := 15 / 4) (m := 5 / 16) (Mb := Mb)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hne (by norm_num)
      hMb1 (five_sixteenth_le_norm_edPolyHermitianTrace_four b hs h1 hb1 hbn T) hmass
    have hlogq : Real.log (Mb / (5 / 16)) = Real.log Mb + Real.log (16 / 5) := by
      rw [div_eq_mul_inv, Real.log_mul (by positivity) (by norm_num)]; congr 1; norm_num
    have hL' : Real.log (8 / (15 / 4 : ℝ)) = L := by dsimp [L]; norm_num
    rw [hlogq, hL', show ((15 / 2 : ℝ) - 1 / 2) = 7 by norm_num] at h
    refine h.trans (le_of_eq ?_)
    dsimp [KH]; field_simp; ring
  have hH1 := hhoriz T₁ hP1
  have hH2 := hhoriz T₂ hP2
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨_, hΨright T₁⟩
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hΨan hΨne
      (by norm_num : (1 / 2 : ℝ) < 15 / 2) hT
      (fun x hx => hP1 x (by rwa [huIccx] at hx))
      (fun x hx => hP2 x (by rwa [huIccx] at hx))
      (fun t _ => hΨright t)
  have hmass0 : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt Ψ w).toNat : ℝ) * (w.re - 1 / 2) := by
    refine Finset.sum_nonneg fun w hw => ?_
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hwlb : 0 ≤ weightedLittlewoodBoundary Ψ (1 / 2) (15 / 2) T₁ T₂ := by
    rw [← hident]; exact mul_nonneg (by positivity) hmass0
  unfold weightedLittlewoodBoundary at hwlb
  rw [show ((15 / 2 : ℝ) - 1 / 2) = 7 by norm_num] at hwlb
  have hlogMb : 0 ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨hfl1, hfl2⟩ := abs_le.mp hfarlog
  obtain ⟨hfd1, hfd2⟩ := abs_le.mp hfarld
  obtain ⟨hh11, hh12⟩ := abs_le.mp hH1
  obtain ⟨hh21, hh22⟩ := abs_le.mp hH2
  have hKL : 0 ≤ KH / L := by positivity
  nlinarith [hKL, hlogMb]

/-- **The Littlewood budget of the Levinson mollified detector for complex mollifiers.** -/
theorem exists_levinson_mollified_budget_complex_le :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ lam : ℝ, |lam| ≤ 1 →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧
          levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite →
        (∃ t ∈ Set.Ioo T₁ T₂,
          levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
        weightedLittlewoodBoundary
            (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)) σ₀ (15 / 2) T₁ T₂
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨KG, hKG, hGhoriz⟩ := exists_horizontal_weighted_levinsonG_bound
  set α : ℝ := Real.log 2
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 22 * Real.exp (-α * (15 / 2)) / α)
  set Cfar' : ℝ := 2 * ((2 * 22 * Real.exp α) * Real.exp (-α * (15 / 2)) / α)
  have hCfar0 : 0 < Cfar := by positivity
  have hCfar'0 : 0 < Cfar' := by positivity
  set Kpsi : ℝ := 2 * (15 / 2 : ℝ) * Real.pi / Real.log (8 / (15 / 4 : ℝ)) with hKpsi
  have hlog2pos : 0 < Real.log (8 / (15 / 4 : ℝ)) := Real.log_pos (by norm_num)
  have hKpsi0 : 0 < Kpsi := by rw [hKpsi]; positivity
  refine ⟨Cfar + (15 / 2) * Cfar' + 2 * (2 * (15 / 2 : ℝ) *
      ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)) + 1,
    2 * KG + 2 * Kpsi + 1, by positivity, by positivity, ?_⟩
  intro lam hlam b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hfin hex hMsq
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hlamC : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hleft : (∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) := by
    have hana : ∀ t ∈ uIcc T₁ T₂,
        AnalyticAt ℂ (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((σ₀ : ℂ) + (t : ℂ) * I) := by
      intro t ht; rw [huIcct] at ht
      exact analyticAt_levinsonMollifiedDetector _ b hs (hne1 σ₀ t (by linarith [ht.1]))
    linarith [integral_log_norm_le_of_meanSquare hT hana hfin hex hMsq]
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re →
      AnalyticAt ℂ (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) z := by
    intro z hz
    refine analyticAt_levinsonMollifiedDetector _ b hs fun hEq => ?_
    rw [hEq, Complex.one_re] at hz; linarith
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s z - 1‖ ≤ 22 * Real.exp (-α * z.re) :=
    fun _ hz => norm_levinsonMollifiedDetector_sub_one_le_exp hlamC b hs h1 hb1 hbn hz.le
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s z - 1‖ ≤ 1 / 2 :=
    fun _ hz => norm_levinsonMollifiedDetector_sub_one_le_half hlamC b hs h1 hb1 hbn hz.le
  have hfarlog : |∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hhoriz : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), edPoly b s ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
          (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
            ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ KG * Real.log T + (Kpsi * Real.log Mb
            + 2 * (15 / 2 : ℝ) *
              ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi)) := by
    intro T hT20 hGne hPne
    have hGana : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
        AnalyticAt ℂ (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I) := fun x _ =>
      analyticAt_levinsonG _ (hne1 x T hT20)
    have hPana : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
        AnalyticAt ℂ (edPoly b s) ((x : ℂ) + (T : ℂ) * I) := fun x _ =>
      (analyticOnNhd_edPoly b hs) _ (Set.mem_univ _)
    have hGi := (continuousOn_weighted_im_logDeriv_horizontal hGana
      (fun x hx => hGne x (by rwa [huIccx] at hx))).intervalIntegrable
    have hPi := (continuousOn_weighted_im_logDeriv_horizontal hPana
      (fun x hx => hPne x (by rwa [huIccx] at hx))).intervalIntegrable
    have hsplit : (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
        (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((x : ℂ) + (T : ℂ) * I)).im)
        = (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
            (logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)).im)
          + ∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
            (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im := by
      rw [← intervalIntegral.integral_add hGi hPi]
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [huIccx] at hx
      have hld : logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
          ((x : ℂ) + (T : ℂ) * I)
          = logDeriv (levinsonG ((lam : ℝ) : ℂ)) ((x : ℂ) + (T : ℂ) * I)
            + logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I) :=
        logDeriv_mul _ (hGne x hx) (hPne x hx)
          (analyticAt_levinsonG _ (hne1 x T hT20)).differentiableAt
          (differentiable_edPoly b hs _)
      rw [hld, Complex.add_im]; ring
    rw [hsplit]
    have hGbound := hGhoriz lam hlam T (by linarith) σ₀ (15 / 2 : ℝ) hσ₀ hσ₀15 le_rfl hGne
    have hPbound := abs_integral_weighted_im_logDeriv_edPoly_complex_le b hs T
      (c := σ₀) (e := (15 / 2 : ℝ)) (r := (15 / 4 : ℝ)) (m := (5 / 16 : ℝ)) (Mb := Mb)
      hσ₀15 (by norm_num) (by norm_num) (by linarith) (by norm_num) hPne (by norm_num) hMb1
      (five_sixteenth_le_norm_edPolyHermitianTrace_four b hs h1 hb1 hbn T) hmass
    have hlogsplit : Real.log (Mb / (5 / 16 : ℝ)) = Real.log Mb + Real.log (16 / 5 : ℝ) := by
      rw [Real.log_div (by linarith) (by norm_num),
        show (16 / 5 : ℝ) = ((5 / 16 : ℝ))⁻¹ by norm_num, Real.log_inv]; ring
    rw [hlogsplit] at hPbound
    have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
    have hPfinal : |∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
        (logDeriv (edPoly b s) ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ Kpsi * Real.log Mb
          + 2 * (15 / 2 : ℝ) *
            ((Real.log (16 / 5 : ℝ) / Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi) := by
      refine hPbound.trans ?_
      have hlog165 : (0 : ℝ) ≤ Real.log (16 / 5 : ℝ) := Real.log_nonneg (by norm_num)
      have hq : (0 : ℝ) ≤ (Real.log Mb + Real.log (16 / 5 : ℝ)) /
          Real.log (8 / (15 / 4 : ℝ)) := div_nonneg (by linarith) hlog2pos.le
      have hnn : (0 : ℝ) ≤ ((Real.log Mb + Real.log (16 / 5 : ℝ)) /
          Real.log (8 / (15 / 4 : ℝ)) + 1) * Real.pi :=
        mul_nonneg (by linarith) Real.pi_pos.le
      have hexpand := mul_le_mul_of_nonneg_right
        (by linarith : 2 * ((15 / 2 : ℝ) - σ₀) ≤ 2 * (15 / 2 : ℝ)) hnn
      refine hexpand.trans (le_of_eq ?_)
      rw [hKpsi]; field_simp; ring
    exact (abs_add_le _ _).trans (by linarith [hGbound, hPfinal])
  have hH1 := hhoriz T₁ h20 hG1 hP1
  have hH2 := hhoriz T₂ (by linarith) hG2 hP2
  have hlogT1 : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log (by linarith) hT.le
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
  unfold weightedLittlewoodBoundary
  have hR : ((15 / 2 : ℝ) - σ₀) * (∫ t in T₁..T₂,
      (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s)
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) ≤ (15 / 2 : ℝ) * Cfar' := by
    have hstep1 := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans hfarld) (by linarith : (0 : ℝ) ≤ (15 / 2 : ℝ) - σ₀)
    have hstep2 := mul_le_mul_of_nonneg_right (by linarith : (15 / 2 : ℝ) - σ₀ ≤ 15 / 2) hCfar'0.le
    linarith
  have hL1 : -(∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ Cfar := by
    linarith [hfarlog, neg_abs_le (∫ t in T₁..T₂,
      Real.log ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s
        (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)]
  have hHa := le_abs_self (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
    (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) ((x : ℂ) + (T₁ : ℂ) * I)).im)
  have hHb := neg_abs_le (∫ x in σ₀..(15 / 2 : ℝ), (x - σ₀) *
    (logDeriv (levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s) ((x : ℂ) + (T₂ : ℂ) * I)).im)
  have hKbound : KG * Real.log T₁ + KG * Real.log T₂ + 2 * Kpsi * Real.log Mb
      ≤ (2 * KG + 2 * Kpsi + 1) * (Real.log T₂ + Real.log Mb) := by
    have hstep := mul_le_mul_of_nonneg_left hlogT1 hKG.le
    nlinarith [hlogT2, hlogMb, hKG.le, hKpsi0.le]
  linarith [hleft, hL1, hR, hH1, hH2, hHa, hHb, hKbound]

/-- **Wide-rectangle horizontal moment of `ζ`-zeros from a complex mollified mean square.** -/
theorem exists_zetaWideMoment_le_of_complex_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc σ₀ (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hbudget⟩ := exists_levinson_mollified_budget_complex_le
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hMsq Z hZ
  set s : Finset ℕ := Finset.Icc 1 N
  have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hlamN : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hG0 : ∀ z : ℂ, levinsonG ((0 : ℝ) : ℂ) z = riemannZeta z := fun z => by simp [levinsonG]
  set Ψ : ℂ → ℂ := edPoly b s
  set g : ℂ → ℂ := levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s
  set F : ℂ → ℂ := fun z => levinsonGEntire ((0 : ℝ) : ℂ) z * Ψ z
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    have hd := norm_edPoly_sub_one_le_half_of_six_le b hs h1mem hb1 hbn
      (z := ((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
    rw [show edPoly b s = Ψ from rfl, h0, show ‖(0 : ℂ) - 1‖ = 1 by simp] at hd
    norm_num at hd
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, hΨright T₁⟩
  have hGeright : ∀ t : ℝ,
      levinsonGEntire ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun _ => levinsonGEntire_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hGright : ∀ t : ℝ,
      levinsonG ((0 : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun _ => levinsonG_ne_zero_of_four_le hlamN (by simp; norm_num)
  have hG1' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := fun x hx => by
    rw [hG0]; exact hG1 x hx
  have hG2' : ∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
      levinsonG ((0 : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := fun x hx => by
    rw [hG0]; exact hG2 x hx
  have hFbot : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ), F ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP1 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20)]; exact hG1' x hx
  have hFtop : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ), F ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP2 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith))]; exact hG2' x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂, F (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => mul_ne_zero (hGeright t) (hΨright t)
  have hGan : AnalyticOnNhd ℂ (levinsonGEntire ((0 : ℝ) : ℂ)) Set.univ :=
    analyticOnNhd_levinsonGEntire _
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz => (hGan z hz).mul (hΨana z hz)
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I, mul_ne_zero (hGeright T₁) (hΨright T₁)⟩
  have hGorder : ∀ w : ℂ, analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hGan ⟨_, hGeright T₁⟩ w
  have hPorder : ∀ w : ℂ, analyticOrderAt Ψ w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hΨana hΨne w
  have hrectfin : {z ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) | F z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hFan hFne
      ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    simpa using h
  have hmemleft : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      ((σ₀ : ℂ) + (t : ℂ) * I) ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) := fun t ht =>
    Complex.mem_reProdIm.mpr ⟨by simp [left_mem_uIcc], by simpa using ht⟩
  have hgFzero : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      (g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 ↔ F ((σ₀ : ℂ) + (t : ℂ) * I) = 0) := by
    intro t ht; rw [huIcct] at ht
    have hzne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
    constructor
    · intro h0
      have hrel : F ((σ₀ : ℂ) + (t : ℂ) * I) =
          (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) := by
        dsimp [F, g, levinsonMollifiedDetector]; rw [levinsonGEntire_eq _ hzne]; ring
      rw [hrel, h0, mul_zero]
    · intro h0
      have hgauge : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hzne
      have heq : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
        rw [← h0]; dsimp [F, g, levinsonMollifiedDetector]; rw [levinsonGEntire_eq _ hzne]; ring
      rcases mul_eq_zero.mp heq with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hgauge
      · exact h
  have hgfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    refine Set.Finite.of_finite_image (Set.Finite.subset hrectfin ?_)
      (fun _ _ _ _ hxy => by simpa using congrArg Complex.im hxy)
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨hmemleft t ht, (hgFzero t ht).mp hz⟩
  have hgex : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_contra hall
    push Not at hall
    exact (Set.Ioo_infinite hT) (hgfin.subset fun t ht =>
      ⟨by rw [huIcct]; exact Set.Ioo_subset_Icc_self ht, hall t ht⟩)
  have hMsq' : (∫ t in T₁..T₂,
      ‖levinsonMollifiedDetector ((0 : ℝ) : ℂ) b s ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq := by
    refine le_trans (le_of_eq (intervalIntegral.integral_congr fun t _ => ?_)) hMsq
    simp only [levinsonMollifiedDetector, hG0]
  have hbud := hbudget 0 (by simp) b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀ hσ₀' h20 hT hG1' hG2' hP1 hP2 hgfin hgex hMsq'
  have hUsub : (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} := by
    intro z hz hEq
    have him := (Complex.mem_reProdIm.mp hz).2
    rw [huIcct, hEq, Complex.one_im] at him; linarith [him.1]
  have hcongrF : weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr isOpen_ne hUsub fun z hz => ?_
    dsimp [F, g, levinsonMollifiedDetector]; rw [levinsonGEntire_eq _ hz]; ring
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul hσ₀15 hT ?_ ?_ ?_ ?_ ?_ hgfin
    · intro hmem; exact hUsub hmem rfl
    · intro z hz; exact analyticAt_levinsonMollifiedDetector _ b hs (hUsub hz)
    · intro x hx; rw [huIccx] at hx; exact mul_ne_zero (hG1' x hx) (hP1 x hx)
    · intro x hx; rw [huIccx] at hx; exact mul_ne_zero (hG2' x hx) (hP2 x hx)
    · intro t _; exact mul_ne_zero (hGright t) (hΨright t)
  obtain ⟨Z', hZ', hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hFan hFne hσ₀15 hT
      hFbot hFtop hFright
  have hsub : Z ⊆ Z' := by
    intro w hw
    obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hw
    refine (hZ' w).mpr ⟨hwmem, ?_⟩
    have hw1 : w ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hwzero)
    dsimp [F]; rw [levinsonGEntire_eq _ hw1, hG0, hwzero]; ring
  have horderG : ∀ w ∈ Z,
      analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w = analyticOrderAt riemannZeta w := by
    intro w hw
    obtain ⟨_, hwzero⟩ := (hZ w).mp hw
    have hw1 : w ≠ 1 := fun h => riemannZeta_one_ne_zero (h ▸ hwzero)
    have hev : levinsonGEntire ((0 : ℝ) : ℂ) =ᶠ[nhds w]
        (fun z : ℂ => (z - 1) ^ 2) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
      rw [Pi.mul_apply, levinsonGEntire_eq _ hz, hG0]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2) w :=
      (analyticAt_id.sub analyticAt_const).pow 2
    rw [analyticOrderAt_congr hev,
      analyticOrderAt_mul hpow_an (analyticAt_riemannZeta_of_ne_one hw1),
      (hpow_an.analyticOrderAt_eq_zero).mpr (pow_ne_zero 2 (sub_ne_zero.mpr hw1)), zero_add]
  have hterm : ∀ w ∈ Z,
      ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
        ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [huIccx] at hre
    have hmul : analyticOrderAt F w
        = analyticOrderAt (levinsonGEntire ((0 : ℝ) : ℂ)) w + analyticOrderAt Ψ w :=
      analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨana w (Set.mem_univ _))
    have hord : ((analyticOrderAt riemannZeta w).toNat : ℝ) ≤ ((analyticOrderAt F w).toNat : ℝ) := by
      rw [hmul, ENat.toNat_add (hGorder w) (hPorder w), ← horderG w hw]
      push_cast; linarith [Nat.cast_nonneg (analyticOrderAt Ψ w).toNat]
    exact mul_le_mul_of_nonneg_right hord (by linarith [hre.1])
  have hZ'nonneg : ∀ w ∈ Z', 0 ≤ ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) := by
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ' w).mp hw).1).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hsum : (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀))
      ≤ ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) :=
    (Finset.sum_le_sum hterm).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w hw _ => hZ'nonneg w hw)
  calc 2 * Real.pi * ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - σ₀)
      ≤ 2 * Real.pi * ∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - σ₀) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂ := hident
    _ = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by rw [hcongrF, hgaugefree]
    _ ≤ _ := hbud

/-- **Left-of-line second-moment floor for arbitrary complex mollifiers.** -/
theorem exists_left_floor_complex :
    ∃ C K₁ : ℝ, 0 < C ∧ 0 < K₁ ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb → (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ a T₁ T₂ : ℝ, 0 < a → a ≤ 1 / 4 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      0 < 2 * Real.pi * (a * ((xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁)) - C -
          K₁ * (Real.log T₂ + Real.log Mb) →
      (T₂ - T₁) * Real.exp (2 / (T₂ - T₁) * (2 * Real.pi * (a * ((xiPosZeroCount T₂ : ℝ) -
          xiPosZeroCount T₁)) - C - K₁ * (Real.log T₂ + Real.log Mb))) ≤
        ∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) (((1 / 2 - a : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨C, K₁, hC, hK₁, hwide⟩ := exists_zetaWideMoment_le_of_complex_mollified_meanSquare
  refine ⟨C, K₁, hC, hK₁, ?_⟩
  intro b N hN hb1 hbn Mb hMb hmass a T₁ T₂ ha0 ha1 h20 hT hG1 hG2 hP1 hP2 hpos
  have hlen : 0 < T₂ - T₁ := by linarith
  set σ₀ : ℝ := 1 / 2 - a with hσ₀
  have hσ₀a : 1 / 4 ≤ σ₀ := by rw [hσ₀]; linarith
  have hσ₀b : σ₀ < 1 / 2 := by rw [hσ₀]; linarith
  have hsub : Set.Icc σ₀ (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc_left hσ₀a
  set I₀ : ℝ := ∫ t in T₁..T₂, ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
    edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hI₀
  obtain ⟨Z, hZ⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT
  have hc := hwide b N hN hb1 hbn Mb hMb hmass σ₀ T₁ T₂ I₀ hσ₀a hσ₀b h20 hT
    (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx))
    (fun x hx => hP1 x (hsub hx)) (fun x hx => hP2 x (hsub hx)) le_rfl Z hZ
  have hbridge := window_count_add_tail_le_zetaWideSum (d := a) ha0.le hT.le Z (by
    rw [← hσ₀]; exact hZ)
  rw [← hσ₀] at hbridge
  have htail : 0 ≤ offLineTail a T₂ - offLineTail a T₁ := sub_nonneg.mpr (offLineTail_mono hT.le)
  set Δ := (xiPosZeroCount T₂ : ℝ) - xiPosZeroCount T₁
  have hchain : 2 * Real.pi * (a * Δ) ≤
      (T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁)) + C + K₁ * (Real.log T₂ + Real.log Mb) := by
    have h1 := mul_le_mul_of_nonneg_left hbridge (by positivity : 0 ≤ 2 * Real.pi)
    have h2 : 0 ≤ 2 * Real.pi * (offLineTail a T₂ - offLineTail a T₁) :=
      mul_nonneg (by positivity) htail
    have h3 : 2 * Real.pi * (a * Δ + (offLineTail a T₂ - offLineTail a T₁)) =
        2 * Real.pi * (a * Δ) + 2 * Real.pi * (offLineTail a T₂ - offLineTail a T₁) := by ring
    linarith
  set E₀ := 2 * Real.pi * (a * Δ) - C - K₁ * (Real.log T₂ + Real.log Mb) with hE₀
  have hlog : E₀ ≤ (T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁)) := by rw [hE₀]; linarith
  have hI₀nn : 0 ≤ I₀ := by
    rw [hI₀]; exact intervalIntegral.integral_nonneg hT.le fun _ _ => by positivity
  have hI₀pos : 0 < I₀ := by
    rcases hI₀nn.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, zero_div, Real.log_zero, mul_zero] at hlog; linarith
  have hexp : 2 / (T₂ - T₁) * E₀ ≤ Real.log (I₀ / (T₂ - T₁)) := by
    have h1 := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / (T₂ - T₁))
    have h2 : 2 / (T₂ - T₁) * ((T₂ - T₁) / 2 * Real.log (I₀ / (T₂ - T₁))) =
        Real.log (I₀ / (T₂ - T₁)) := by field_simp
    linarith
  have h3 := Real.exp_le_exp.mpr hexp
  rw [Real.exp_log (by positivity), le_div_iff₀ hlen] at h3
  linarith

/-- **Off-line first moment from a complex mollified mean square on `σ₀ ∈ [1/4, 1/2)`.** -/
theorem exists_zetaOffLineFirstMoment_le_of_complex_mollified_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  classical
  obtain ⟨C, K, hC, hK, hwide⟩ := exists_zetaWideMoment_le_of_complex_mollified_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hMsq Z hZ
  obtain ⟨Z', hZ'⟩ := exists_zetaWideRectangleZeros_finset (σ₀ := σ₀) h20 hT
  have hw := hwide b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hMsq Z' hZ'
  have hsub : Z ⊆ Z' := by
    intro z hz
    obtain ⟨hmem, hζ⟩ := (hZ z).mp hz
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hmem
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    refine (hZ' z).mpr ⟨Complex.mem_reProdIm.mpr ⟨?_, him⟩, hζ⟩
    rw [uIcc_of_le (by linarith : σ₀ ≤ 15 / 2)]
    exact ⟨hσ₀'.le.trans hre.1, hre.2⟩
  have hterm : ∀ z ∈ Z,
      ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - 1 / 2) ≤
        ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - σ₀) := by
    intro z _
    exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
  have hnn : ∀ z ∈ Z', 0 ≤ ((analyticOrderAt riemannZeta z).toNat : ℝ) * (z.re - σ₀) := by
    intro z hz
    have hre := (Complex.mem_reProdIm.mp ((hZ' z).mp hz).1).1
    rw [uIcc_of_le (by linarith : σ₀ ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hsum := (Finset.sum_le_sum hterm).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun z hz _ => hnn z hz)
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans hw

/-- **Off-line first moment from the complex mollified mean square on the critical line.** -/
theorem exists_zetaOffLineFirstMoment_le_of_complex_line_meanSquare :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        2 * Real.pi *
            (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
          ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
              + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaOffLineFirstMoment_le_of_complex_mollified_meanSquare
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq Z hZ
  have hlen : (0 : ℝ) < T₂ - T₁ := by linarith
  set m : ℝ → ℝ := fun σ : ℝ => ∫ t in T₁..T₂,
      ‖riemannZeta ((lineClamp σ : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) ((lineClamp σ : ℂ) + (t : ℂ) * I)‖ ^ 2 with hm
  have hmcont : Continuous m := continuous_clamped_meanSquare b N T₁ T₂
  have hmhalf : m (1 / 2) ≤ Msq := by
    simp only [hm]; rw [lineClamp_of_mem (by norm_num)]; exact hMsq
  have hstep : ∀ ε : ℝ, 0 < ε →
      2 * Real.pi *
          (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
        ≤ (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁))
            + C + K * (Real.log T₂ + Real.log Mb) := by
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := Metric.continuousAt_iff.mp hmcont.continuousAt ε hε
    set σ₀ : ℝ := max (1 / 4) (1 / 2 - δ / 2) with hσ₀def
    have hσ₀ : 1 / 4 ≤ σ₀ := le_max_left _ _
    have hσ₀' : σ₀ < 1 / 2 := by rw [hσ₀def]; exact max_lt (by norm_num) (by linarith)
    have hdist : dist σ₀ (1 / 2) < δ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith, by linarith [le_max_right (1 / 4 : ℝ) (1 / 2 - δ / 2)]⟩
    have hmσ₀ : m σ₀ ≤ Msq + ε := by
      have h := hδε hdist
      rw [Real.dist_eq, abs_sub_lt_iff] at h
      linarith [h.1, hmhalf]
    have hmσ₀' : (∫ t in T₁..T₂,
        ‖riemannZeta ((σ₀ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 N) ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq + ε := by
      simpa only [hm, lineClamp_of_mem ⟨hσ₀, hσ₀'.le⟩] using hmσ₀
    have hsub : Set.Icc σ₀ (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
      Set.Icc_subset_Icc hσ₀ le_rfl
    exact hmain b N hN hb1 hbn Mb hMb1 hmass σ₀ T₁ T₂ (Msq + ε) hσ₀ hσ₀' h20 hT
      (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx))
      (fun x hx => hP1 x (hsub hx)) (fun x hx => hP2 x (hsub hx)) hmσ₀' Z hZ
  have hlim : Tendsto (fun ε : ℝ =>
      (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
      (𝓝[>] 0) (𝓝 ((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
        + C + K * (Real.log T₂ + Real.log Mb))) := by
    have hcont : ContinuousAt (fun ε : ℝ =>
        (T₂ - T₁) / 2 * Real.log ((Msq + ε) / (T₂ - T₁)) + C + K * (Real.log T₂ + Real.log Mb))
        0 := by
      have hlog : ContinuousAt (fun ε : ℝ => Real.log ((Msq + ε) / (T₂ - T₁))) 0 :=
        ContinuousAt.comp (g := Real.log)
          (Real.continuousAt_log (by simp only [add_zero]; exact (div_pos hMsqpos hlen).ne'))
          (by fun_prop)
      exact ((continuousAt_const.mul hlog).add continuousAt_const).add continuousAt_const
    have h := hcont.tendsto; simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hstep ε hε

/-- **Critical-line log-mean sandwich for arbitrary complex mollifiers.** -/
theorem exists_zetaLine_logMean_complex_sandwich :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ Msq →
        -(C + K * Real.log T₂) ≤
            (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ∧
          (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
            ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
                + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hedge⟩ := exists_zetaLine_littlewood_edge_budget
  obtain ⟨C₂, K₂, hC₂, hK₂, hmoment⟩ := exists_zetaOffLineFirstMoment_le_of_complex_line_meanSquare
  refine ⟨C₁ + C₂, K₁ + K₂, by positivity, by positivity, ?_⟩
  intro b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq
  have hsub : Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc (by norm_num) le_rfl
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset h20 hT
  have h1 := hedge T₁ T₂ h20 hT (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx)) Z hZ
  have h2 := hmoment b N hN hb1 hbn Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos
    hG1 hG2 hP1 hP2 hMsq Z hZ
  have hmass0 : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    refine Finset.sum_nonneg fun w hw => ?_
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  exact ⟨by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hmass0], by nlinarith⟩

/-- **Log-integral ceiling on `[T, 2T]` from any complex mollified second moment.** -/
theorem exists_logIntegral_le_of_complex_secondMoment :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ T : ℝ, 22 ≤ T → ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
      (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) → ∀ ε : ℝ, 0 ≤ ε →
      (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T →
      (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
        ε / 2 * T + C + K * (Real.log T + Real.log N) := by
  obtain ⟨C₀, K₀, hC₀, hK₀, hs⟩ := exists_zetaLine_logMean_complex_sandwich
  obtain ⟨Cz, hCz0, hCz⟩ := exists_norm_riemannZeta_le_leftStrip
  refine ⟨1 + C₀ + K₀ + 2 * Real.log (Cz + 1) + 8, 5 * K₀ + 4, ?_, by positivity, ?_⟩
  · linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ Cz + 1)]
  intro T hT b N hN hb1 hb ε hε hsecond
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  obtain ⟨T₁, ⟨hT₁a, hT₁b⟩, T₂, ⟨hT₂a, hT₂b⟩, hs1, hs2⟩ :=
    exists_admissible_slices (b := b) (N := N) hN hb1 hb
      (A₁ := T) (B₁ := T + 1) (A₂ := 2 * T - 1) (B₂ := 2 * T)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hT12 : T₁ < T₂ := by linarith
  have hcont := continuous_norm_sq_zeta_mul_edPoly b N (c := 1 / 2) (by norm_num)
  have hMsq : (∫ t in T₁..T₂, ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ (1 + ε) * T :=
    (intervalIntegral.integral_mono_interval hT₁a.le hT12.le hT₂b.le
      (Filter.Eventually.of_forall fun _ => by positivity)
      (hcont.intervalIntegrable _ _)).trans hsecond
  have hMsq0 : 0 < (1 + ε) * T := by positivity
  have hMb1 : (1 : ℝ) ≤ (N : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast hN)
  have hsw := (hs b N hN hb1 hb ((N : ℝ) ^ 5) hMb1 (sum_norm_mul_rpow_four_le hb)
    T₁ T₂ ((1 + ε) * T) (by linarith) hT12 hMsq0
    (fun x hx => (hs1 x hx).1) (fun x hx => (hs2 x hx).1)
    (fun x hx => (hs1 x hx).2) (fun x hx => (hs2 x hx).2) hMsq).2
  have hL0 : 0 < T₂ - T₁ := by linarith
  have hjensen : (T₂ - T₁) / 2 * Real.log ((1 + ε) * T / (T₂ - T₁)) ≤ ε / 2 * T + 1 := by
    have h2 := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hMsq0 hL0)) (by positivity : 0 ≤ (T₂ - T₁) / 2)
    have h3 : (T₂ - T₁) / 2 * ((1 + ε) * T / (T₂ - T₁) - 1) = ((1 + ε) * T - (T₂ - T₁)) / 2 := by
      field_simp
    rw [h3] at h2
    linarith [show (1 + ε) * T = T + ε * T by ring, show ε / 2 * T = ε * T / 2 by ring]
  have hlogT₂ : Real.log T₂ ≤ Real.log T + 1 := by
    have h1 : Real.log T₂ ≤ Real.log (2 * T) := Real.log_le_log (by linarith) hT₂b.le
    rw [Real.log_mul two_ne_zero hT0.ne'] at h1
    linarith [Real.log_two_lt_d9]
  have hlogMb : Real.log ((N : ℝ) ^ 5) = 5 * Real.log N := by rw [Real.log_pow]; norm_num
  have hlog3 : Real.log 3 ≤ 2 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  set Y : ℝ := Real.log (Cz + 1) + 2 * Real.log 3 + 2 * Real.log T with hY
  have hCz1 : 0 ≤ Real.log (Cz + 1) := Real.log_nonneg (by linarith)
  have hlog30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hpoint : ∀ t ∈ Icc T (2 * T),
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ Y := by
    intro t ht
    by_cases h0 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ = 0
    · rw [h0, Real.log_zero]; exact hY0
    have hpos : 0 < ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h1 := hCz (1 / 2) t (by norm_num) (by norm_num)
    rw [abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)] at h1
    have h2 : ((1 + t) : ℝ) ^ 2 ≤ (3 * T) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2
    have h3 : ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (Cz + 1) * (3 * T) ^ 2 :=
      h1.trans (mul_le_mul (by linarith) h2 (by positivity) (by linarith))
    refine (Real.log_le_log hpos h3).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) hT0.ne', hY]
    push_cast; ring
  have htail : ∀ a c : ℝ, T ≤ a → a ≤ c → c ≤ 2 * T → c - a ≤ 1 →
      (∫ t in a..c, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤ Y := by
    intro a c ha hac hc hlen
    have h1 := intervalIntegral.integral_mono_on hac
      (intervalIntegrable_log_norm_riemannZeta_line a c) intervalIntegrable_const
      fun t ht => hpoint t ⟨ha.trans ht.1, ht.2.trans hc⟩
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    exact h1.trans ((mul_le_mul_of_nonneg_right hlen hY0).trans_eq (one_mul Y))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_norm_riemannZeta_line T T₁)
    (intervalIntegrable_log_norm_riemannZeta_line T₁ T₂)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_log_norm_riemannZeta_line T T₂)
    (intervalIntegrable_log_norm_riemannZeta_line T₂ (2 * T))
  have ht1 := htail T T₁ le_rfl hT₁a.le (by linarith) (by linarith)
  have ht2 := htail T₂ (2 * T) (by linarith) hT₂b.le le_rfl (by linarith)
  rw [hlogMb] at hsw
  rw [← hsplit2, ← hsplit]
  rw [hY] at ht1 ht2
  have hK1 : K₀ * (Real.log T₂ + 5 * Real.log N) ≤ K₀ * (Real.log T + 1 + 5 * Real.log N) :=
    mul_le_mul_of_nonneg_left (by linarith) hK₀.le
  have hK2 : K₀ * Real.log T ≤ 5 * K₀ * Real.log T :=
    mul_le_mul_of_nonneg_right (by linarith) hlogT
  have hexp : (5 * K₀ + 4) * (Real.log T + Real.log N) =
      5 * K₀ * Real.log T + 5 * K₀ * Real.log N + 4 * Real.log T + 4 * Real.log N := by ring
  have hexp2 : K₀ * (Real.log T + 1 + 5 * Real.log N) =
      K₀ * Real.log T + K₀ + 5 * K₀ * Real.log N := by ring
  rw [hexp]; linarith

/-- Complex-coefficient mollified second moment tending to `1` at length `exp(o(T))`. -/
def ComplexMollifiedSecondMomentLaw : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
    (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧ Real.log N ≤ ε * T ∧
    (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ (1 + ε) * T

/-- Complex-coefficient mollified second moment with excess `K₀ / log T` at length
`exp(T / log T)`. -/
def ComplexSecondMomentRate (K₀ : ℝ) : Prop :=
  ∀ᶠ T : ℝ in atTop, ∃ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N ∧ b 1 = 1 ∧
    (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) ∧ Real.log N ≤ T / Real.log T ∧
    (∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
        (1 + K₀ / Real.log T) * T

/-- **Complex mollified second moment tending to `1` implies `(L)`.** -/
theorem logMean_tendsto_zero_of_complexMollifiedSecondMomentLaw
    (h : ComplexMollifiedSecondMomentLaw) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ t in T..(2 * T),
      Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) atTop (𝓝 0) := by
  obtain ⟨C, K, hC, hK, hup⟩ := exists_logIntegral_le_of_complex_secondMoment
  obtain ⟨C', K', hC', hK', hlow⟩ := exists_logIntegral_floor
  rw [Metric.tendsto_nhds]
  intro η hη
  set ε : ℝ := η / (4 * (1 / 2 + K)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεK : ε / 2 + K * ε = η / 4 := by rw [hε]; field_simp
  have hlog1 := eventually_log_pow_mul_exp_le 1 (c := 1)
    (ε := η / (8 * (K + K'))) one_pos (by positivity)
  filter_upwards [h ε hε0, hlog1, eventually_ge_atTop (22 : ℝ),
    eventually_ge_atTop (8 * (C + C' + K') / η)] with T hlaw hl hT22 hTC
  obtain ⟨b, N, hN, hb1, hb, hlogN, hmom⟩ := hlaw
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hu := hup T hT22 b N hN hb1 hb ε hε0.le hmom
  have hd := hlow T (by linarith)
  have hlogT' : (K + K') * Real.log T ≤ η / 8 * T := by
    have hTe : Real.exp (-(1 * Real.log T)) = T⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hT0]
    rw [hTe, pow_one, ← div_eq_mul_inv, div_le_iff₀ hT0] at hl
    exact (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ K + K')).trans (by field_simp; rfl)
  have hTC' : C + C' + K' ≤ η / 8 * T := by linarith [(div_le_iff₀ hη).mp hTC]
  have hlog2T : Real.log (2 * T) ≤ Real.log T + 1 := by
    rw [Real.log_mul two_ne_zero hT0.ne']; linarith [Real.log_two_lt_d9]
  have hup2 : (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ≤
      η / 2 * T := by
    have h1 : K * (Real.log T + Real.log N) ≤ K * Real.log T + K * (ε * T) := by
      rw [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogN hK.le)
    have h2 : ε / 2 * T + K * (ε * T) = η / 4 * T := by rw [← hεK]; ring
    have hKK : K * Real.log T + K' * Real.log T = (K + K') * Real.log T := by ring
    have hK'0 : 0 ≤ K' * Real.log T := by positivity
    linarith [show 0 < C' + K' by positivity]
  have hlow2 : -(η / 2 * T) ≤
      ∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
    have h1 : K' * Real.log (2 * T) ≤ K' * Real.log T + K' :=
      (mul_le_mul_of_nonneg_left hlog2T hK'.le).trans_eq (by ring)
    have hKK : K * Real.log T + K' * Real.log T = (K + K') * Real.log T := by ring
    have hK0 : 0 ≤ K * Real.log T := by positivity
    have hpos_ηT : 0 < η * T := by positivity
    linarith
  rw [Real.dist_eq, sub_zero, abs_mul, abs_of_pos (inv_pos.mpr hT0)]
  have h5 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hlow2, hup2⟩) (inv_pos.mpr hT0).le
  have h6 : T⁻¹ * (η / 2 * T) = η / 2 := by field_simp
  linarith

/-- **`100%` critical-scale clustering from complex long mollifiers.** -/
theorem criticalClustering_of_complexMollifiedSecondMomentLaw
    (h : ComplexMollifiedSecondMomentLaw) (κ : ℝ) (hκ : 0 < κ) :
    Tendsto (fun V : ℝ => _root_.RHTower.offLineCountBeyond (κ / Real.log V) V /
      (V * Real.log V)) atTop (𝓝 0) := by
  have hTFAE := criticalClustering_logMean_mollifier_hecke_tfae
    (c := 1 / 4) (by norm_num) (by norm_num)
  exact (hTFAE.out 0 4).mp (logMean_tendsto_zero_of_complexMollifiedSecondMomentLaw h) κ hκ

/-- **`ComplexSecondMomentRate K₀` implies `LogFreeNearLineZeroDensity` (`D_zero`).** -/
theorem logFreeNearLineZeroDensity_of_complexSecondMomentRate {K₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (h : ComplexSecondMomentRate K₀) :
    LogFreeNearLineZeroDensity := by
  obtain ⟨C, K, hC, hK, hup⟩ := exists_logIntegral_le_of_complex_secondMoment
  obtain ⟨C', K', hC', hK', hbud⟩ := exists_zetaLine_littlewood_edge_budget_all_heights
  set K₁ : ℝ := K₀ / 2 + K + 1 with hK₁
  refine ⟨fun A => K₁ / Real.pi / A, tendsto_const_nhds.div_atTop tendsto_id, fun A hA => ?_⟩
  set D : ℝ := C + C' + K' + K + K' + 1 with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  filter_upwards [h, eventually_log_pow_mul_exp_le 2 (c := 1) (ε := 1 / D) one_pos (by positivity),
    eventually_ge_atTop (22 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1] with
    V hrate hsm hV22 hℓ
  obtain ⟨b, N, hN, hb1, hb, hlogN, hmom⟩ := hrate
  have hV0 : 0 < V := by linarith
  have hℓ0 : 0 < Real.log V := by linarith
  have hu := hup V hV22 b N hN hb1 hb _ (by positivity) hmom
  have hbudget := (abs_le.mp (hbud V (by linarith))).1
  set M : ℝ := ∑ z ∈ (shellZeros V (2 * V)).filter (fun z => 1 / 2 < z.re),
      ((analyticOrderAt _root_.RHTower.xi z).toNat : ℝ) * (z.re - 1 / 2) with hM
  rw [← hM] at hbudget
  have hsm2 : D * Real.log V ^ 2 ≤ V := by
    have hTe : Real.exp (-(1 * Real.log V)) = V⁻¹ := by
      rw [one_mul, Real.exp_neg, Real.exp_log hV0]
    rw [hTe, ← div_eq_mul_inv, div_le_iff₀ hV0] at hsm
    exact (mul_le_mul_of_nonneg_left hsm hD0.le).trans (by field_simp; rfl)
  have hVdiv : D * Real.log V ≤ V / Real.log V := by
    rw [le_div_iff₀ hℓ0]
    calc D * Real.log V * Real.log V = D * Real.log V ^ 2 := by ring
      _ ≤ V := hsm2
  have hlog2V : Real.log (2 * V) ≤ Real.log V + 1 := by
    rw [Real.log_mul two_ne_zero hV0.ne']; linarith [Real.log_two_lt_d9]
  have hsum : 2 * Real.pi * M ≤ K₁ * (V / Real.log V) := by
    have h1 : K * (Real.log V + Real.log N) ≤ K * Real.log V + K * (V / Real.log V) := by
      rw [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogN hK.le)
    have h2 : K' * Real.log (2 * V) ≤ K' * Real.log V + K' :=
      (mul_le_mul_of_nonneg_left hlog2V hK'.le).trans_eq (by ring)
    have h3 : K₀ / Real.log V / 2 * V = K₀ / 2 * (V / Real.log V) := by ring
    have h4 : K₁ * (V / Real.log V) =
        K₀ / 2 * (V / Real.log V) + K * (V / Real.log V) + V / Real.log V := by rw [hK₁]; ring
    have h5 : C + C' + K' + (K + K') * Real.log V ≤ D * Real.log V := by
      have h6 : C + C' + K' ≤ (C + C' + K') * Real.log V :=
        le_mul_of_one_le_right (by positivity) hℓ
      rw [hD]; linarith
    linarith
  have hfold := sum_order_filter_abs_le (V₁ := V) (V₂ := 2 * V) (x := A / Real.log V) (by positivity)
  rw [← hM] at hfold
  refine hfold.trans ?_
  have hval : 2 / (A / Real.log V) * M = Real.log V / (Real.pi * A) * (2 * Real.pi * M) := by
    field_simp
  rw [hval]
  calc Real.log V / (Real.pi * A) * (2 * Real.pi * M)
      ≤ Real.log V / (Real.pi * A) * (K₁ * (V / Real.log V)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = K₁ / Real.pi / A * V := by field_simp

/-- **`ComplexSecondMomentRate K₀` implies `LogFreeNearLineWindowOccupancy` (`D_win`).** -/
theorem logFreeNearLineWindowOccupancy_of_complexSecondMomentRate {K₀ : ℝ}
    (hK₀ : 0 ≤ K₀) (h : ComplexSecondMomentRate K₀) :
    LogFreeNearLineWindowOccupancy :=
  (logFreeNearLineZeroDensity_implies_windowOccupancy_and_logMean
    (logFreeNearLineZeroDensity_of_complexSecondMomentRate hK₀ h)).1
