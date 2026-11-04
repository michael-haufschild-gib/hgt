import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindows
import GaloisForLFunctions.ZeroConfigurationGeometry.PerturbedLatticeProducts
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AnnihilatingTestsForSparseSpectra
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge

/-!
# Blind windows for perturbed lattices

Every bounded perturbation of a lattice is blinded at the density aperture.

**Theorem** (`exists_window_blind_to_perturbed_lattice`). Let `ν_k` be real with `|ν_k − kh| ≤ L`
for all `k ∈ ℤ`. For every aperture `r > π/h` and every `z₀` off the `ν_k` there is a window of
aperture `r` whose transform vanishes at every `ν_k` and not at `z₀`.

The density of the `ν_k` is `1/h`, so `π/h` is the Jensen aperture, and for `L = 0` it is sharp
(`exists_window_blind_to_lattice_iff`). No separation of the `ν_k` and no smallness of `L` is
needed. Convolution adds apertures and multiplies transforms (`apertureWindow_convolution`), so
finite unions of perturbed lattices of total density `D` are blinded at every aperture `> πD`
(`exists_window_blind_to_perturbed_lattices`).

Construction. Shift the lattice to `μ_k = (k + θ)h` with `θ` avoiding the countably many
coincidences. Start from a smooth window with transform `sin((π/h)(w − θh)) b̂(w)`. For each
`|k| ≤ N` divide at `μ_k` and multiply by `c_k(w − ν_k)` (`exists_smooth_window_div`, the
differential window); the support never grows (`exists_stage_window`). On the real line the
transform of the stage-`N` window is `sin · b̂ · Π_{|k| ≤ N} r_k`, bounded by `K(1 + |x|)^p |b̂(x)|`
uniformly in `N` (`norm_sin_mul_prod_pertFactor_le`), and `b̂` decays faster than any power
(`exists_pow_mul_norm_paperFT_le`). By dominated convergence the stage windows converge uniformly
to a continuous window `f` of the same support, whose transform is the pointwise limit: it vanishes
at every `ν_k` and equals `sin · b̂ · Π_k r_k ≠ 0` at `z₀`. Convolving `f` with a bump makes it
smooth.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate Convolution

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23

/-! ### Transform rules -/

theorem paperFT_const_mul' (c : ℂ) (f : ℝ → ℂ) (w : ℂ) :
    paperFT (fun u => c * f u) w = c * paperFT f w := by
  rw [paperFT_def, paperFT_def, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun u => by ring)

/-- Iterated derivatives multiply the transform by `(−iw)^j`. -/
theorem iterate_deriv_props {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv^[j] b) ∧ HasCompactSupport (deriv^[j] b) ∧
      ∀ w, paperFT (deriv^[j] b) w = (-(I * w)) ^ j * paperFT b w := by
  induction j with
  | zero => exact ⟨hb, hbc, fun w => by simp⟩
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨(contDiff_infty_iff_deriv.mp h1).2, h2.deriv, fun w => ?_⟩
    rw [_root_.RHTower.EvenSector.paperFT_deriv_of_compact (h1.of_le (by exact_mod_cast le_top)) h2,
      h3, pow_succ]
    ring

theorem norm_paperFT_ofReal_le_integral {g : ℝ → ℂ} (x : ℝ) :
    ‖paperFT g x‖ ≤ ∫ u, ‖g u‖ := by
  rw [paperFT_def]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1 with u
  rw [norm_mul, show I * (x : ℂ) * (u : ℂ) = ((x * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The transform of a smooth window decays faster than any power** on the real line. -/
theorem exists_pow_mul_norm_paperFT_le {b : ℝ → ℂ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, (1 + |x|) ^ m * ‖paperFT b x‖ ≤ C := by
  set M0 := ∫ u, ‖b u‖
  set Mm := ∫ u, ‖deriv^[m] b u‖
  have hM0 : 0 ≤ M0 := integral_nonneg fun _ => norm_nonneg _
  have hMm : 0 ≤ Mm := integral_nonneg fun _ => norm_nonneg _
  refine ⟨2 ^ m * (M0 + Mm), by positivity, fun x => ?_⟩
  obtain ⟨-, -, hft⟩ := iterate_deriv_props hb hbc m
  have h0 := norm_paperFT_ofReal_le_integral (g := b) x
  have hm : |x| ^ m * ‖paperFT b x‖ ≤ Mm := by
    have := norm_paperFT_ofReal_le_integral (g := deriv^[m] b) x
    rw [hft, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hpow : (1 + |x|) ^ m ≤ 2 ^ m * (1 + |x| ^ m) := by
    rcases le_total |x| 1 with hx | hx
    · calc (1 + |x|) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ ≤ 2 ^ m * (1 + |x| ^ m) := le_mul_of_one_le_right (by positivity)
            (by linarith [pow_nonneg (abs_nonneg x) m])
    · calc (1 + |x|) ^ m ≤ (2 * |x|) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
        _ = 2 ^ m * |x| ^ m := mul_pow _ _ _
        _ ≤ 2 ^ m * (1 + |x| ^ m) := by nlinarith [pow_nonneg (two_pos.le : (0 : ℝ) ≤ 2) m]
  calc (1 + |x|) ^ m * ‖paperFT b x‖ ≤ 2 ^ m * (1 + |x| ^ m) * ‖paperFT b x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 2 ^ m * (‖paperFT b x‖ + |x| ^ m * ‖paperFT b x‖) := by ring
    _ ≤ 2 ^ m * (M0 + Mm) := by gcongr

/-! ### The stage windows -/

/-- **Stage windows.** For a smooth window `f₀` of aperture `A` whose transform vanishes on the
lattice `μ_k`, and every finite `S ⊂ ℤ`, there is a smooth window of aperture `A` with
`Π_{k ∈ S}(w − μ_k) · f̂(w) = Π_{k ∈ S} c_k(w − ν_k) · f̂₀(w)`, `c_k = (i − μ_k)/(i − ν_k)`. -/
theorem exists_stage_window {h θ A : ℝ} (hh : 0 < h) (hA : 0 ≤ A) (ν : ℤ → ℂ) {f₀ : ℝ → ℂ}
    (hf₀ : ContDiff ℝ (⊤ : ℕ∞) f₀) (hf₀s : tsupport f₀ ⊆ Icc (-A) A)
    (hf₀z : ∀ k : ℤ, paperFT f₀ (latPt h θ k) = 0) (S : Finset ℤ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ tsupport f ⊆ Icc (-A) A ∧
      ∀ w : ℂ, (∏ k ∈ S, (w - latPt h θ k)) * paperFT f w =
        (∏ k ∈ S, (I - latPt h θ k) / (I - ν k) * (w - ν k)) * paperFT f₀ w := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨f₀, hf₀, hf₀s, fun w => by simp⟩
  | insert j S hj ih =>
    obtain ⟨f, hf, hfs, hfw⟩ := ih
    -- the transform of `f` vanishes at `μ_j`
    have hzero : paperFT f (latPt h θ j) = 0 := by
      have h1 := hfw (latPt h θ j)
      rw [hf₀z j, mul_zero] at h1
      have hne : ∏ k ∈ S, ((latPt h θ j : ℂ) - latPt h θ k) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro k hk h0
        have hjk : j ≠ k := fun e => hj (e ▸ hk)
        have := latPt_sep (θ := θ) hh hjk
        rw [← Complex.ofReal_sub, Complex.ofReal_eq_zero] at h0
        rw [h0, abs_zero] at this
        linarith
      exact (mul_eq_zero.mp h1).resolve_left hne
    obtain ⟨g, hg, hgs, hgw⟩ := exists_smooth_window_div hA hf hfs hzero
    have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    set c : ℂ := (I - latPt h θ j) / (I - ν j)
    refine ⟨fun u => c * annihilate (ν j) g u, contDiff_const.mul (contDiff_annihilate hg),
      (tsupport_mul_subset_right (f := fun _ => c)).trans
        ((tsupport_annihilate_subset _ g).trans hgs), fun w => ?_⟩
    rw [paperFT_const_mul', paperFT_annihilate hg hgc, Finset.prod_insert hj,
      Finset.prod_insert hj]
    have := hfw w
    rw [hgw w] at this
    linear_combination (c * (w - ν j)) * this

/-- Off the lattice the stage transform is `f̂₀ · Π_{k ∈ S} r_k`. -/
theorem stage_eq_prod {h θ : ℝ} (ν : ℤ → ℂ) {f f₀ : ℝ → ℂ} {S : Finset ℤ}
    (hfw : ∀ w : ℂ, (∏ k ∈ S, (w - latPt h θ k)) * paperFT f w =
      (∏ k ∈ S, (I - latPt h θ k) / (I - ν k) * (w - ν k)) * paperFT f₀ w)
    {w : ℂ} (hw : ∀ k, w ≠ latPt h θ k) :
    paperFT f w = paperFT f₀ w * ∏ k ∈ S, pertFactor h θ ν k w := by
  have hne : ∏ k ∈ S, (w - latPt h θ k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hw k)
  have e : ∏ k ∈ S, pertFactor h θ ν k w =
      (∏ k ∈ S, (I - latPt h θ k) / (I - ν k) * (w - ν k)) / ∏ k ∈ S, (w - latPt h θ k) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [pertFactor]
    ring
  rw [e, mul_div_assoc', eq_div_iff hne]
  linear_combination hfw w

/-- A window of aperture `A` bounded by `M` has transform at most `2AM e^{A|Im z|}`. -/
theorem norm_paperFT_le_of_tsupport {g : ℝ → ℂ} {A M : ℝ} (hA : 0 ≤ A)
    (hgs : tsupport g ⊆ Icc (-A) A) (hM : ∀ u, ‖g u‖ ≤ M) (z : ℂ) :
    ‖paperFT g z‖ ≤ M * Real.exp (A * |z.im|) * (2 * A) := by
  rw [paperFT_def, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-A) A)
    fun u hu => by rw [eq_zero_of_not_mem_Icc_of_tsupport hgs hu, zero_mul]]
  have hvol : (volume : Measure ℝ).real (Icc (-A) A) = 2 * A := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [← hvol]
  refine norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top fun u hu => ?_
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul (hM u) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
    ((norm_nonneg _).trans (hM u))
  have hre : (I * z * u).re = -(z.im * u) := by simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have := abs_le.mpr hu
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ |z.im| * A := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = A * |z.im| := mul_comm _ _

/-! ### The limit window -/

/-- **The limit window.** The stage windows of `f₀ = sin((π/h)(· − θh)) b̂` converge uniformly
to a continuous window of the same aperture, blind to every `ν_j`, whose transform off the lattice is
`f̂₀ Π_k r_k`. -/
theorem exists_blind_limit_window {h θ L A : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) (hA : 0 ≤ A)
    {ν : ℤ → ℂ} (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2)
    {b f₀ : ℝ → ℂ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b)
    (hf₀ : ContDiff ℝ (⊤ : ℕ∞) f₀) (hf₀s : tsupport f₀ ⊆ Icc (-A) A)
    (hf₀t : ∀ w : ℂ, paperFT f₀ w =
      Complex.sin (((π / h : ℝ) : ℂ) * (w - ((θ * h : ℝ) : ℂ))) * paperFT b w)
    (hνlat : ∀ j k, ν j ≠ latPt h θ k) :
    ∃ f : ℝ → ℂ, Continuous f ∧ tsupport f ⊆ Icc (-A) A ∧ (∀ j, paperFT f (ν j) = 0) ∧
      ∀ z : ℂ, (∀ k, z ≠ latPt h θ k) →
        paperFT f z = paperFT f₀ z * ∏' k, pertFactor h θ ν k z := by
  classical
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hf₀z : ∀ k : ℤ, paperFT f₀ (latPt h θ k) = 0 := fun k => by
    rw [hf₀t, show ((π / h : ℝ) : ℂ) * ((latPt h θ k : ℝ) - ((θ * h : ℝ) : ℂ)) = k * π by
      rw [latPt]; push_cast; field_simp; ring, Complex.sin_int_mul_pi, zero_mul]
  -- the stage windows over `[−N, N]`
  set S : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) N with hS
  choose F hF hFs hFw using fun N => exists_stage_window hh hA ν hf₀ hf₀s hf₀z (S N)
  have hFc : ∀ N, HasCompactSupport (F N) := fun N =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hFs N)
  have hStend : Tendsto S atTop atTop := Filter.tendsto_atTop_finset_of_monotone
    (fun N M hNM => Finset.Icc_subset_Icc (by simp [hNM]) (by simp [hNM]))
    (fun k => ⟨k.natAbs, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩)
  have hprod : ∀ w : ℂ, (∀ k, w ≠ latPt h θ k) → Tendsto (fun N => ∏ k ∈ S N, pertFactor h θ ν k w)
      atTop (𝓝 (∏' k, pertFactor h θ ν k w)) := fun w hw =>
    (multipliable_pertFactor hh hθ hL him hw).hasProd.comp hStend
  have hFeq : ∀ N (w : ℂ), (∀ k, w ≠ latPt h θ k) →
      paperFT (F N) w = paperFT f₀ w * ∏ k ∈ S N, pertFactor h θ ν k w :=
    fun N w hw => stage_eq_prod ν (hFw N) hw
  -- domination on the real line
  set K := nearestConst h L * Real.exp (2 * L * nearFarConst h L) with hK
  set p := 2 * L * (4 * (1 + L) / h) with hp
  set n := ⌈p⌉₊ with hn
  obtain ⟨C, hC0, hC⟩ := exists_pow_mul_norm_paperFT_le hb hbc (n + 2)
  have hK0 : 0 ≤ K := by
    rw [hK]; unfold nearestConst; positivity
  set D : ℝ → ℝ := fun x => K * C * (1 + x ^ 2)⁻¹ with hD
  have hDint : Integrable D := (integrable_inv_one_add_sq.const_mul (K * C))
  have hdom : ∀ N (x : ℝ), (∀ k, (x : ℂ) ≠ latPt h θ k) → ‖paperFT (F N) x‖ ≤ D x := by
    intro N x hx
    have hx' : ∀ k, x ≠ latPt h θ k := fun k e => hx k (by rw [e])
    rw [hFeq N x hx, hf₀t,
      show Complex.sin (((π / h : ℝ) : ℂ) * ((x : ℂ) - ((θ * h : ℝ) : ℂ))) =
        ((Real.sin (π / h * (x - θ * h)) : ℝ) : ℂ) by push_cast; ring_nf]
    have hbound := norm_sin_mul_prod_pertFactor_le hh hθ hL him (S N) x hx'
    have h1 : (1 : ℝ) ≤ 1 + |x| := by linarith [abs_nonneg x]
    have hpn : (1 + |x|) ^ p ≤ (1 + |x|) ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil p)
    have hbx := hC x
    have hsq : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    calc ‖((Real.sin (π / h * (x - θ * h)) : ℝ) : ℂ) * paperFT b x *
          ∏ k ∈ S N, pertFactor h θ ν k x‖
        = ‖((Real.sin (π / h * (x - θ * h)) : ℝ) : ℂ) * ∏ k ∈ S N, pertFactor h θ ν k x‖ *
            ‖paperFT b x‖ := by rw [mul_right_comm, norm_mul]
      _ ≤ K * (1 + |x|) ^ n * ‖paperFT b x‖ := by
          gcongr
          exact hbound.trans (mul_le_mul_of_nonneg_left hpn hK0)
      _ = K * ((1 + |x|) ^ n * ‖paperFT b x‖) := by ring
      _ ≤ K * (C / (1 + |x|) ^ 2) := by
          gcongr
          rw [le_div_iff₀ (by positivity)]
          calc (1 + |x|) ^ n * ‖paperFT b x‖ * (1 + |x|) ^ 2 =
              (1 + |x|) ^ (n + 2) * ‖paperFT b x‖ := by ring
            _ ≤ C := hbx
      _ ≤ D x := by
          have hKC : 0 ≤ K * C := mul_nonneg hK0 hC0
          calc K * (C / (1 + |x|) ^ 2) = K * C / (1 + |x|) ^ 2 := by ring
            _ ≤ K * C / (1 + x ^ 2) := div_le_div_of_nonneg_left hKC (by positivity) hsq
            _ = D x := by rw [hD, div_eq_mul_inv]
  have hnull : ∀ᵐ x : ℝ, ∀ k, (x : ℂ) ≠ latPt h θ k := by
    have hcount : (Set.range fun k : ℤ => latPt h θ k).Countable := Set.countable_range _
    filter_upwards [hcount.ae_notMem volume] with x hx k e
    exact hx ⟨k, by exact_mod_cast e.symm⟩
  -- the limit transform
  set G : ℝ → ℂ := fun x => paperFT f₀ x * ∏' k, pertFactor h θ ν k x with hG
  have hconv : ∀ᵐ x : ℝ, Tendsto (fun N => paperFT (F N) x) atTop (𝓝 (G x)) := by
    filter_upwards [hnull] with x hx
    refine (tendsto_congr fun N => (hFeq N x hx).symm).mp ?_
    exact (hprod x hx).const_mul _
  have hFcont : ∀ N, Continuous fun x : ℝ => paperFT (F N) x := fun N =>
    ArithmeticCastelnuovoSeveri.continuous_paperFT_ofReal
      ((hF N).continuous.integrable_of_hasCompactSupport (hFc N))
  have hFint : ∀ N, Integrable fun x : ℝ => paperFT (F N) x := fun N =>
    hDint.mono' (hFcont N).aestronglyMeasurable (by
      filter_upwards [hnull] with x hx using hdom N x hx)
  have hGmeas : AEStronglyMeasurable G :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hFcont N).aestronglyMeasurable) hconv
  have hGint : Integrable G := hDint.mono' hGmeas (by
    filter_upwards [hnull, hconv] with x hx hxc
    exact le_of_tendsto' (hxc.norm) fun N => hdom N x hx)
  have hL1 : Tendsto (fun N => ∫ x : ℝ, ‖paperFT (F N) x - G x‖) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (fun x => 2 * D x)
      (fun N => ((hFint N).sub hGint).aestronglyMeasurable.norm) (hDint.const_mul 2)
      (fun N => by
        filter_upwards [hnull, hconv] with x hx hxc
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        show ‖paperFT (F N) x - G x‖ ≤ 2 * D x
        have hGx : ‖G x‖ ≤ D x := le_of_tendsto' (hxc.norm) fun M => hdom M x hx
        linarith [norm_sub_le (paperFT (F N) x) (G x), hdom N x hx])
      (by
        filter_upwards [hconv] with x hxc
        have := (tendsto_sub_nhds_zero_iff.mpr hxc).norm
        simpa using this)
    simpa using this
  -- inversion and uniform convergence
  set f : ℝ → ℂ := ArithmeticCastelnuovoSeveri.invFT G with hf
  have hsup : ∀ N u, ‖F N u - f u‖ ≤ (2 * π)⁻¹ * ∫ x : ℝ, ‖paperFT (F N) x - G x‖ := by
    intro N u
    rw [ArithmeticCastelnuovoSeveri.eq_invFT_paperFT (hF N).continuous
      ((hF N).continuous.integrable_of_hasCompactSupport (hFc N)) (hFint N) u]
    exact ArithmeticCastelnuovoSeveri.norm_invFT_sub_le (hFint N) hGint u
  have hsup0 : Tendsto (fun N => (2 * π)⁻¹ * ∫ x : ℝ, ‖paperFT (F N) x - G x‖) atTop (𝓝 0) := by
    simpa using hL1.const_mul (2 * π)⁻¹
  have hunif : TendstoUniformly F f atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(hsup0.eventually (gt_mem_nhds hε))] with N hN u
    rw [dist_eq_norm, norm_sub_rev]
    exact (hsup N u).trans_lt hN
  have hfc : Continuous f :=
    hunif.continuous (Eventually.of_forall fun N => (hF N).continuous).frequently
  -- the support
  have hpt : ∀ u, Tendsto (fun N => F N u) atTop (𝓝 (f u)) := fun u => hunif.tendsto_at u
  have hfs : tsupport f ⊆ Icc (-A) A := closure_minimal (fun u hu => by
    by_contra hout
    apply hu
    refine tendsto_nhds_unique (hpt u) ?_
    exact tendsto_const_nhds.congr fun N =>
      (eq_zero_of_not_mem_Icc_of_tsupport (hFs N) hout).symm) isClosed_Icc
  have hfcs : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  -- transforms converge everywhere
  have htrans : ∀ z : ℂ, Tendsto (fun N => paperFT (F N) z) atTop (𝓝 (paperFT f z)) := by
    intro z
    have hb : ∀ N, ‖paperFT (F N) z - paperFT f z‖ ≤
        (2 * π)⁻¹ * (∫ x : ℝ, ‖paperFT (F N) x - G x‖) * (Real.exp (A * |z.im|) * (2 * A)) := by
      intro N
      have hsub : paperFT (F N) z - paperFT f z = paperFT (fun u => F N u + (-1) * f u) z := by
        rw [paperFT_add_smul (hF N).continuous (hFc N) hfc hfcs]; ring
      rw [hsub]
      refine (norm_paperFT_le_of_tsupport (M := (2 * π)⁻¹ * ∫ x : ℝ, ‖paperFT (F N) x - G x‖)
        hA ?_ (fun u => ?_) z).trans (le_of_eq (by ring))
      · exact (tsupport_add _ _).trans (Set.union_subset (hFs N)
          ((tsupport_mul_subset_right (f := fun _ => (-1 : ℂ))).trans hfs))
      · rw [show F N u + -1 * f u = F N u - f u by ring]
        exact hsup N u
    have hlim : Tendsto (fun N => (2 * π)⁻¹ * (∫ x : ℝ, ‖paperFT (F N) x - G x‖) *
        (Real.exp (A * |z.im|) * (2 * A))) atTop (𝓝 0) := by
      simpa using hsup0.mul_const (Real.exp (A * |z.im|) * (2 * A))
    exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun N => norm_nonneg _) hb hlim)
  refine ⟨f, hfc, hfs, fun j => ?_, ?_⟩
  · -- blind to every `ν_j`
    refine tendsto_nhds_unique (htrans (ν j)) (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop j.natAbs] with N hN
    have hj : j ∈ S N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h1 := hFw N (ν j)
    have hz : ∏ k ∈ S N, (I - latPt h θ k) / (I - ν k) * (ν j - ν k) = 0 :=
      Finset.prod_eq_zero hj (by rw [sub_self, mul_zero])
    rw [hz, zero_mul] at h1
    have hne : ∏ k ∈ S N, (ν j - latPt h θ k) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => sub_ne_zero.mpr (hνlat j k)
    exact ((mul_eq_zero.mp h1).resolve_left hne).symm
  · -- the transform off the lattice
    intro z hz
    refine tendsto_nhds_unique (htrans z) ?_
    refine (tendsto_congr fun N => (hFeq N z hz).symm).mp ?_
    exact (hprod z hz).const_mul _

/-! ### Smoothing and the theorem -/

/-- Convolving a window of aperture `A` with a bump of aperture `ε` gives aperture `A + ε`. -/
theorem convolution_eq_zero_of_lt {f β : ℝ → ℂ} {A ε : ℝ} (hfs : tsupport f ⊆ Icc (-A) A)
    (hβs : tsupport β ⊆ Icc (-ε) ε) {u : ℝ} (hu : A + ε < |u|) :
    convolution f β (ContinuousLinearMap.mul ℝ ℂ) volume u = 0 := by
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply', Pi.zero_apply]
  by_cases hft : f t = 0
  · rw [hft, zero_mul]
  · by_cases hβt : β (u - t) = 0
    · rw [hβt, mul_zero]
    · exfalso
      obtain ⟨h1, h2⟩ := hfs (subset_tsupport _ hft)
      obtain ⟨h3, h4⟩ := hβs (subset_tsupport _ hβt)
      rcases lt_abs.mp hu with h | h <;> linarith

/-- **Blind windows for complex perturbations of a lattice.** Let `ν_k ∈ ℂ` with
`|ν_k − kh| ≤ L` and `|Im ν_k| ≤ 1/2` for all `k ∈ ℤ`. For every aperture `r > π/h` and every `z₀`
off the `ν_k` there is a window of aperture `r` whose transform vanishes at every `ν_k` and not at
`z₀`. -/
theorem exists_window_blind_to_complex_perturbed_lattice {h L r : ℝ} (hh : 0 < h)
    (hr : π / h < r) (ν : ℤ → ℂ) (hν : ∀ k : ℤ, ‖ν k - k * h‖ ≤ L)
    (him : ∀ k, |(ν k).im| ≤ 1 / 2) {z₀ : ℂ} (hz₀ : ∀ k, z₀ ≠ ν k) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ k, paperFT f (ν k) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  -- a lattice shift avoiding all coincidences
  set E : Set ℝ := (Set.range fun q : ℤ × ℤ => (ν q.1).re / h - q.2) ∪
    Set.range fun k : ℤ => z₀.re / h - k with hE
  have hEc : E.Countable := (Set.countable_range _).union (Set.countable_range _)
  obtain ⟨θ, ⟨hθ0, hθ1⟩, hθE⟩ :=
    SquareRootThreshold.exists_mem_Ioo_notMem_of_countable (by norm_num : (0 : ℝ) < 1) hEc
  have hθ : |θ| ≤ 1 := by rw [abs_of_pos hθ0]; linarith
  have hνlat : ∀ j k, ν j ≠ latPt h θ k := by
    intro j k e
    apply hθE
    refine Or.inl ⟨(j, k), ?_⟩
    simp only [e, Complex.ofReal_re, latPt]
    field_simp
    ring
  have hz₀lat : ∀ k, z₀ ≠ latPt h θ k := by
    intro k e
    apply hθE
    refine Or.inr ⟨k, ?_⟩
    simp only [e, Complex.ofReal_re, latPt]
    field_simp
    ring
  have hL' : ∀ k, ‖ν k - latPt h θ k‖ ≤ L + h := by
    intro k
    have := hν k
    rw [latPt, show ν k - ((((k : ℝ) + θ) * h : ℝ) : ℂ) = (ν k - k * h) - ((θ * h : ℝ) : ℂ) by
      push_cast; ring]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < θ * h)]
    nlinarith
  -- the sine window
  set ε := (r - π / h) / 3 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨b, hb, hbc, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hε0 z₀
  have hbw : ApertureWindow ε b := ⟨hb.of_le (by norm_cast), hbs⟩
  obtain ⟨hf₀w, hf₀t⟩ := sineShift_props (τ := θ * h) (by positivity : (0 : ℝ) ≤ π / h) hbw
  have hf₀ : ContDiff ℝ (⊤ : ℕ∞) (sineShift (π / h) (θ * h) b) := contDiff_sineShift _ _ hb
  -- the limit window
  obtain ⟨f, hfc, hfs, hfν, hfz'⟩ := exists_blind_limit_window hh hθ (by positivity) hL' him hb hbc
    hf₀ hf₀w.2 hf₀t hνlat
  have hfz := hfz' z₀ hz₀lat
  -- smoothing
  obtain ⟨β, hβ, hβc, hβs, hβ1⟩ := exists_smooth_window_paperFT_eq_one hε0 z₀
  have hfcs : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hfs
  set F := convolution f β (ContinuousLinearMap.mul ℝ ℂ) volume with hF
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F :=
    hβc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hfc.locallyIntegrable hβ
  have hFs : tsupport F ⊆ Icc (-r) r := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hout
    apply hu
    refine convolution_eq_zero_of_lt hfs hβs ?_
    by_contra hle
    push Not at hle
    apply hout
    have := abs_le.mp hle
    constructor <;> linarith
  have hFt : ∀ z, paperFT F z = paperFT f z * paperFT β z := fun z =>
    _root_.RHTower.WeilHerglotz.paperFT_convolution (hfc.integrable_of_hasCompactSupport hfcs)
      (hβ.continuous.integrable_of_hasCompactSupport hβc) hfcs hβc z
  refine ⟨F, ⟨hFsmooth.of_le (by norm_cast), hFs⟩, fun k => by
    rw [hFt, hfν k, zero_mul], ?_⟩
  rw [hFt, hβ1, mul_one, hfz, hf₀t, hb1, mul_one]
  refine mul_ne_zero ?_ (tprod_pertFactor_ne_zero hh hθ hL' him hz₀lat hz₀)
  intro h0
  obtain ⟨n, hn⟩ := Complex.sin_eq_zero_iff.mp h0
  apply hz₀lat n
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  rw [latPt]
  push_cast at hn ⊢
  field_simp at hn
  linear_combination hn

/-- **Blind windows for perturbed lattices.** Let `ν_k` be real with `|ν_k − kh| ≤ L` for all
`k ∈ ℤ`. For every aperture `r > π/h` and every `z₀` off the `ν_k` there is a window of aperture
`r` whose transform vanishes at every `ν_k` and not at `z₀`. -/
theorem exists_window_blind_to_perturbed_lattice {h L r : ℝ} (hh : 0 < h) (hr : π / h < r)
    (ν : ℤ → ℝ) (hν : ∀ k : ℤ, |ν k - k * h| ≤ L) {z₀ : ℂ} (hz₀ : ∀ k, z₀ ≠ ν k) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ k, paperFT f (ν k) = 0) ∧ paperFT f z₀ ≠ 0 :=
  exists_window_blind_to_complex_perturbed_lattice hh hr (fun k => (ν k : ℂ))
    (fun k => by
      rw [show (ν k : ℂ) - k * h = ((ν k - k * h : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs]
      exact hν k)
    (fun k => by simp) hz₀

/-- Convolution of two windows: apertures add and transforms multiply. -/
theorem apertureWindow_convolution {f g : ℝ → ℂ} {A B : ℝ} (hf : ApertureWindow A f)
    (hg : ApertureWindow B g) :
    ApertureWindow (A + B) (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) ∧
      ∀ z, paperFT (convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume) z =
        paperFT f z * paperFT g z := by
  have hfc := hf.hasCompactSupport
  have hgc := hg.hasCompactSupport
  refine ⟨⟨hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      hf.1.continuous.locallyIntegrable hg.1, ?_⟩, fun z =>
    _root_.RHTower.WeilHerglotz.paperFT_convolution
      (hf.1.continuous.integrable_of_hasCompactSupport hfc)
      (hg.1.continuous.integrable_of_hasCompactSupport hgc) hfc hgc z⟩
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hout
  apply hu
  refine convolution_eq_zero_of_lt hf.2 hg.2 ?_
  by_contra hle
  push Not at hle
  apply hout
  have := abs_le.mp hle
  constructor <;> linarith

/-- **Finite unions of perturbed lattices at the density aperture.** For finitely many bounded
perturbations `ν_j` of lattices `h_jℤ`, of total density `D = Σ_j 1/h_j`, every aperture
`r > πD` has a window blind to all `ν_j(k)` that sees any given `z₀` off them. -/
theorem exists_window_blind_to_perturbed_lattices {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℝ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, |ν j k - k * h j| ≤ L j) {r : ℝ}
    (hr : π * ∑ j ∈ T, (h j)⁻¹ < r) {z₀ : ℂ} (hz₀ : ∀ j ∈ T, ∀ k, z₀ ≠ ν j k) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧ (∀ j ∈ T, ∀ k, paperFT f (ν j k) = 0) ∧
      paperFT f z₀ ≠ 0 := by
  classical
  set δ := (r - π * ∑ j ∈ T, (h j)⁻¹) / (T.card + 1) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by positivity)
  have key : ∀ U ⊆ T, ∃ f : ℝ → ℂ, ApertureWindow (δ + ∑ j ∈ U, (π / h j + δ)) f ∧
      (∀ j ∈ U, ∀ k, paperFT f (ν j k) = 0) ∧ paperFT f z₀ ≠ 0 := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      obtain ⟨b, hb, -, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hδ0 z₀
      refine ⟨b, ?_, by simp, by rw [hb1]; exact one_ne_zero⟩
      rw [Finset.sum_empty, add_zero]
      exact ⟨hb.of_le (by norm_cast), hbs⟩
    | insert j U hj ih =>
      intro hsub
      obtain ⟨f, hf, hfz, hf0⟩ := ih ((Finset.subset_insert j U).trans hsub)
      have hjT := hsub (Finset.mem_insert_self j U)
      obtain ⟨g, hg, hgz, hg0⟩ := exists_window_blind_to_perturbed_lattice (hh j hjT)
        (show π / h j < π / h j + δ by linarith) (ν j) (hν j hjT) (hz₀ j hjT)
      obtain ⟨hw, hwt⟩ := apertureWindow_convolution hf hg
      refine ⟨convolution f g (ContinuousLinearMap.mul ℝ ℂ) volume, ?_, fun i hi k => ?_, ?_⟩
      · rw [Finset.sum_insert hj]
        convert hw using 1
        ring
      · rw [hwt]
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rw [hgz k, mul_zero]
        · rw [hfz i hi k, zero_mul]
      · rw [hwt]; exact mul_ne_zero hf0 hg0
  obtain ⟨f, hf, hfz, hf0⟩ := key T le_rfl
  have hap : δ + ∑ j ∈ T, (π / h j + δ) = r := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hδ]
    have hc : (T.card : ℝ) + 1 ≠ 0 := by positivity
    rw [show ∑ j ∈ T, π / h j = π * ∑ j ∈ T, (h j)⁻¹ by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
    field_simp
    ring
  exact ⟨f, hap ▸ hf, hfz, hf0⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
