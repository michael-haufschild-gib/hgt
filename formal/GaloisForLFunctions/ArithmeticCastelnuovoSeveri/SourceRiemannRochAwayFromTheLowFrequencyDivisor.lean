import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheNearRadicalOfZetaIsFiniteDimensional
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# Riemann–Roch for `ℤ` away from the low-frequency divisor

The programme asks for an effectivity on the scaling surface defined without the sign of the form,
ample by its definition, with Riemann–Roch supply proved from that definition. The `L²` source
cone `l2SourceCone c V = {x : 0 ≤ x·H, 0 ≤ x·V, c∫f² ≤ 2(x·H)(x·V)}` is defined from the source and
is ample for `c > 0`; its Riemann–Roch axiom on a test space `V` is exactly the coercive floor
`c∫f² ≤ W(f, f)` (`l2SourceCone_riemannRoch_iff_weilPair_ge`). On all tests of aperture `a` no
positive `c` survives beyond `c ≤ K exp((11/2)a − πe^{2(a−2)})` (the corpus Gaussian ceiling), even
under RH: near radicals are low-frequency tests with tiny Weil energy.

**Theorem** (`lowBlindTests_effectivity`). At every degree `a > 0`, on the scaling subsurface of
real aperture-`a` tests whose transforms vanish at the pole `i/2` and on the low-frequency grid
`D_a = {j h(a) : |j| ≤ J(a)}`, the `L²` source cone with `c_a = E(a)(1 − 1/π)`, `E = 10 + 68e^a`,
satisfies the Riemann–Roch axiom and the ample axiom, the subsurface satisfies the Hodge index, and
it is not trivial. Unconditionally.

The mechanism (`re_W_zeta_ge_of_lowGrid`): the band inequality
`Re W(f, f) ≥ E‖f‖² − (E/π)∫_{−T}^{T}|h_f|²` (`re_W_zeta_ge_band`) and the grid bound
`∫_{−T}^{T}|h_f|² ≤ ‖f‖²` (`integral_band_le_of_lowGridOf`) give `Re W(f, f) ≥ E(1 − 1/π)‖f‖²`.
Nontriviality (`exists_ne_zero_mem_lowBlindTests`): `2#D_a + 3` real translates of a bump are
linearly independent, and the `2#D_a + 2` real conditions leave a nonzero combination.

So Riemann–Roch with a source effectivity holds for `ℤ` at every degree on a subsurface of finite
codimension, with a coercivity constant that grows like `e^a` instead of decaying doubly
exponentially: the Gaussian ceiling, and with it everything the Hodge index of `ℤ` still has to
decide, sits on the finitely many directions read by the samples on `D_a` and at the pole. Over
`𝔽_q` no finite divisor works for the golden fake curve (`goldenDatum_no_finite_divisor`).
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### Coercivity away from the divisor -/

/-- The coercivity constant `c_a = E(a)(1 − 1/π)`, `E(a) = 10 + 68e^a`. -/
def lowBlindCoercivity (a : ℝ) : ℝ := RHTower.horizonExponent (Real.exp (2 * a)) * (1 - 1 / π)

theorem lowBlindCoercivity_pos (a : ℝ) : 0 < lowBlindCoercivity a := by
  have hE := RHTower.horizonExponent_pos (Real.exp (2 * a))
  have hπ : 1 / π < 1 := by
    rw [div_lt_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  unfold lowBlindCoercivity
  exact mul_pos hE (by linarith)

/-- **Coercivity away from the low-frequency divisor.** If `f ∈ C²` is supported in `[−a, a]` and
its transform vanishes at `i/2` and on the grid `D_a`, then `Re W_ζ(f, f) ≥ E(a)(1 − 1/π)‖f‖²`. -/
theorem re_W_zeta_ge_of_lowGrid {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) (hp : paperFT f (I / 2) = 0)
    (hgrid : ∀ j ∈ lowGrid a, paperFT f (((j : ℝ) * gridStep a : ℝ) : ℂ) = 0) :
    lowBlindCoercivity a * ∫ u, ‖f u‖ ^ 2 ≤ (zetaZeroConfig.W f f).re := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hband := re_W_zeta_ge_band hf hfs hp
  have hJ := integral_band_le_of_lowGridOf (horizonFreq_nonneg a) ha hf.continuous hfc hfs hgrid
  have hE := RHTower.horizonExponent_pos (Real.exp (2 * a))
  have hπ := Real.pi_pos
  have hEπ : 0 ≤ RHTower.horizonExponent (Real.exp (2 * a)) / π := (div_pos hE hπ).le
  have hmono := mul_le_mul_of_nonneg_left hJ hEπ
  unfold lowBlindCoercivity
  have : RHTower.horizonExponent (Real.exp (2 * a)) * (1 - 1 / π) * (∫ u, ‖f u‖ ^ 2) =
      RHTower.horizonExponent (Real.exp (2 * a)) * (∫ u, ‖f u‖ ^ 2) -
        RHTower.horizonExponent (Real.exp (2 * a)) / π * (∫ u, ‖f u‖ ^ 2) := by ring
  rw [this]
  linarith

/-! ### The low-frequency-blind subsurface -/

theorem tsupport_cx (g : ℝ → ℝ) : tsupport (cx g) = tsupport g :=
  tsupport_comp_eq (g := fun x : ℝ => (x : ℂ)) (by simp) g

/-- The real aperture-`a` tests blind to the pole and to the low-frequency grid `D_a`. -/
def lowBlindTests (a : ℝ) : Submodule ℝ realTests where
  carrier := {f | tsupport f.1 ⊆ Icc (-a) a ∧ paperFT (cx f.1) (I / 2) = 0 ∧
    ∀ j ∈ lowGrid a, paperFT (cx f.1) (((j : ℝ) * gridStep a : ℝ) : ℂ) = 0}
  add_mem' := by
    rintro f g ⟨hfs, hfp, hfg⟩ ⟨hgs, hgp, hgg⟩
    have hf := f.2
    have hg := g.2
    have hadd : ∀ z, paperFT (cx (f + g : realTests).1) z = paperFT (cx f.1) z + paperFT (cx g.1) z :=
      fun z => by
        rw [Submodule.coe_add, cx_add]
        exact paperFT_add (cx_contDiff hf.1).continuous (cx_hasCompactSupport hf.2)
          (cx_contDiff hg.1).continuous (cx_hasCompactSupport hg.2) z
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · refine closure_minimal (fun u hu => ?_) isClosed_Icc
      by_contra hu'
      apply hu
      simp only [Submodule.coe_add, Pi.add_apply]
      rw [image_eq_zero_of_notMem_tsupport fun h => hu' (hfs h),
        image_eq_zero_of_notMem_tsupport fun h => hu' (hgs h), add_zero]
    · rw [hadd, hfp, hgp, add_zero]
    · rw [hadd, hfg j hj, hgg j hj, add_zero]
  zero_mem' := by
    have h0 : ∀ z, paperFT (cx ((0 : realTests) : ℝ → ℝ)) z = 0 := fun z => by
      simp [cx, paperFT]
    refine ⟨?_, h0 _, fun j _ => h0 _⟩
    simp
  smul_mem' := by
    rintro c f ⟨hfs, hfp, hfg⟩
    have hsmul : ∀ z, paperFT (cx (c • f : realTests).1) z = (c : ℂ) * paperFT (cx f.1) z :=
      fun z => by rw [Submodule.coe_smul, cx_smul, paperFT_smul]
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · refine closure_minimal (fun u hu => ?_) isClosed_Icc
      by_contra hu'
      apply hu
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [image_eq_zero_of_notMem_tsupport fun h => hu' (hfs h), mul_zero]
    · rw [hsmul, hfp, mul_zero]
    · rw [hsmul, hfg j hj, mul_zero]

/-- On the low-frequency-blind tests the source floor holds with `c_a = E(a)(1 − 1/π)`. -/
theorem lowBlindCoercivity_le_weilPair {a : ℝ} (ha : 0 ≤ a) (f : lowBlindTests a) :
    lowBlindCoercivity a * ∫ u : ℝ, (f.1.1 u) ^ 2 ≤ weilPair f.1.1 f.1.1 := by
  obtain ⟨hfs, hfp, hfg⟩ := f.2
  have hd := cx_contDiff f.1.2.1
  have hc := cx_hasCompactSupport f.1.2.2
  have hcs : tsupport (cx f.1.1) ⊆ Icc (-a) a := by rw [tsupport_cx]; exact hfs
  have h := re_W_zeta_ge_of_lowGrid ha hd hcs hfp hfg
  have hW : (zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re = weilPair f.1.1 f.1.1 := by
    rw [weilPair, RHTower.zeta_W_eq_weilFullFunctional_mixed hd hc hd hc]
  have hn : ∫ u, ‖cx f.1.1 u‖ ^ 2 = ∫ u : ℝ, (f.1.1 u) ^ 2 := by
    congr 1
    funext u
    rw [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hW, hn] at h
  exact h

/-! ### Nontriviality -/

theorem cx_injective_fun {g : ℝ → ℝ} (hg : g ≠ 0) : cx g ≠ 0 := by
  intro h
  apply hg
  funext u
  have := congrFun h u
  simpa [cx] using this

/-- Real translates of a nonzero compactly supported function are `ℝ`-linearly independent. -/
theorem linearIndependent_real_translate {N : ℕ} {s : Fin N → ℝ} (hs : Function.Injective s)
    {g : ℝ → ℝ} (hgc : HasCompactSupport g) (hg0 : g ≠ 0) :
    LinearIndependent ℝ fun i => fun u => g (u - s i) := by
  have hC := linearIndependent_translate hs (cx_hasCompactSupport hgc) (cx_injective_fun hg0)
  rw [Fintype.linearIndependent_iff] at hC ⊢
  intro c hc i
  have hc' : ∑ i, (c i : ℂ) • translate (s i) (cx g) = 0 := by
    funext u
    have h := congrFun hc u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, translate, cx]
    exact_mod_cast h
  exact_mod_cast hC (fun i => (c i : ℂ)) hc' i

/-- **The low-frequency-blind subsurface is not trivial** at any degree `a > 0`. -/
theorem exists_ne_zero_mem_lowBlindTests {a : ℝ} (ha : 0 < a) :
    ∃ f : lowBlindTests a, (f : realTests) ≠ 0 := by
  classical
  set G := lowGrid a with hG
  set K := Fintype.card (Option G) with hK
  set N := 2 * K + 1 with hN
  -- a `C²` bump with support in `(−a/2, a/2)`
  have hnhd : Ioo (-(a / 2)) (a / 2) ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) (by linarith)
  obtain ⟨g, hgs, hgc, hgd, -, hg0⟩ := exists_contDiff_tsupport_subset (n := 2) hnhd
  have hgne : g ≠ 0 := fun h => by simp [h] at hg0
  -- shifts in `[−a/2, a/2]`
  set s : Fin N → ℝ := fun i => -(a / 2) + i * (a / N) with hsdef
  have hNpos : (0 : ℝ) < N := by positivity
  have hstep : 0 < a / N := div_pos ha hNpos
  have hsinj : Function.Injective s := by
    intro i j hij
    simp only [hsdef, add_right_inj] at hij
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hstep.ne' hij)
  have hs_mem : ∀ i, -(a / 2) ≤ s i ∧ s i ≤ a / 2 := by
    intro i
    have hi : (i : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    have h1 : 0 ≤ (i : ℝ) * (a / N) := by positivity
    have h2 : (i : ℝ) * (a / N) ≤ a := by
      calc (i : ℝ) * (a / N) ≤ N * (a / N) := mul_le_mul_of_nonneg_right hi hstep.le
        _ = a := by field_simp
    constructor <;> simp only [hsdef] <;> linarith
  set v : Fin N → ℝ → ℝ := fun i u => g (u - s i) with hv
  have hvd : ∀ i, ContDiff ℝ 2 (v i) := fun i => hgd.comp (contDiff_id.sub contDiff_const)
  have hvs : ∀ i, tsupport (v i) ⊆ Icc (-a) a := by
    intro i
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - s i ∈ Ioo (-(a / 2)) (a / 2) := hgs (subset_tsupport g hu)
    obtain ⟨hs0, hs1⟩ := hs_mem i
    exact ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
  have hvc : ∀ i, HasCompactSupport (v i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hvs i)
  have hli : LinearIndependent ℝ v := linearIndependent_real_translate hsinj hgc hgne
  -- the real conditions
  let pt : Option G → ℂ := fun k =>
    match k with
    | none => I / 2
    | some j => ((((j : ℤ) : ℝ) * gridStep a : ℝ) : ℂ)
  let L : (Fin N → ℝ) →ₗ[ℝ] (Option G → ℂ) :=
    { toFun := fun c k => ∑ i, (c i : ℂ) * paperFT (cx (v i)) (pt k)
      map_add' := fun c d => by
        funext k
        simp only [Pi.add_apply, Complex.ofReal_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext k
        simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
          Complex.real_smul, Finset.mul_sum, mul_assoc] }
  have hdim : Module.finrank ℝ (Option G → ℂ) < Module.finrank ℝ (Fin N → ℝ) := by
    rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, smul_eq_mul, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨c, hcker, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  set f : ℝ → ℝ := ∑ i, c i • v i with hfdef
  have hfmem : f ∈ realTests := by
    refine ⟨?_, ?_⟩
    · have he : f = fun u => ∑ i, c i * v i u := by
        funext u
        simp [hfdef]
      rw [he]
      exact ContDiff.sum fun i _ => (hvd i).const_smul (c i)
    · refine IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) ?_
      refine closure_minimal (fun u hu => ?_) isClosed_Icc
      by_contra hu'
      apply hu
      simp only [hfdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [image_eq_zero_of_notMem_tsupport fun h => hu' (hvs i h), mul_zero]
  have hcxf : cx f = ∑ i, (c i : ℂ) • cx (v i) := by
    funext u
    simp [hfdef, cx]
  have hFT : ∀ z, paperFT (cx f) z = ∑ i, (c i : ℂ) * paperFT (cx (v i)) z := fun z => by
    rw [hcxf, paperFT_sum_smul (fun i => cx (v i)) (fun i => (cx_contDiff (hvd i)).continuous)
      (fun i => cx_hasCompactSupport (hvc i))]
  have hLc : ∀ k, ∑ i, (c i : ℂ) * paperFT (cx (v i)) (pt k) = 0 := fun k => congrFun hcker k
  have hfs : tsupport f ⊆ Icc (-a) a := by
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    by_contra hu'
    apply hu
    simp only [hfdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [image_eq_zero_of_notMem_tsupport fun h => hu' (hvs i h), mul_zero]
  refine ⟨⟨⟨f, hfmem⟩, hfs, ?_, fun j hj => ?_⟩, ?_⟩
  · rw [hFT]; exact hLc none
  · rw [hFT]; exact hLc (some ⟨j, hj⟩)
  · intro h0
    have hf0 : f = 0 := congrArg Subtype.val h0
    have := (Fintype.linearIndependent_iff.mp hli) c hf0
    exact hc0 (funext this)

/-! ### The effectivity -/

/-- **Riemann–Roch for `ℤ` away from the low-frequency divisor.** At every degree `a > 0`, on the
scaling subsurface of real aperture-`a` tests blind to the pole and to the grid `D_a`, the `L²`
source cone with `c_a = E(a)(1 − 1/π) > 0` satisfies the Riemann–Roch axiom and the ample axiom,
the subsurface satisfies the Hodge index, and its Weil form is positive on a nonzero test. -/
theorem lowBlindTests_effectivity {a : ℝ} (ha : 0 < a) :
    (scalingSubsurface (lowBlindTests a)).RiemannRochAxiom
        (l2SourceCone (lowBlindCoercivity a) (lowBlindTests a)) ∧
      (scalingSubsurface (lowBlindTests a)).AmpleAxiom
        (l2SourceCone (lowBlindCoercivity a) (lowBlindTests a)) ∧
      (scalingSubsurface (lowBlindTests a)).HodgeIndex ∧
      ∃ f : lowBlindTests a, 0 < weilPair f.1.1 f.1.1 := by
  have hc := lowBlindCoercivity_pos a
  have hfloor := lowBlindCoercivity_le_weilPair ha.le
  refine ⟨(l2SourceCone_riemannRoch_iff_weilPair_ge hc _).mpr hfloor, l2SourceCone_ample hc _,
    (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mpr fun f =>
      le_trans (mul_nonneg hc.le (integral_nonneg fun _ => sq_nonneg _)) (hfloor f), ?_⟩
  obtain ⟨f, hf0⟩ := exists_ne_zero_mem_lowBlindTests ha
  refine ⟨f, lt_of_lt_of_le (mul_pos hc ?_) (hfloor f)⟩
  -- a nonzero continuous test has positive `L²` mass
  have hcont : Continuous fun u => (f.1.1 u) ^ 2 := (f.1.2.1.continuous).pow 2
  have hint : Integrable fun u => (f.1.1 u) ^ 2 := by
    have h : Integrable fun u => f.1.1 u * f.1.1 u :=
      (f.1.2.1.continuous.mul f.1.2.1.continuous).integrable_of_hasCompactSupport f.1.2.2.mul_right
    simpa only [← pow_two] using h
  refine lt_of_le_of_ne (integral_nonneg fun _ => sq_nonneg _) (fun h => hf0 ?_)
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hint).mp h.symm
  have hz : (fun u => (f.1.1 u) ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq volume hcont continuous_const).mp hae
  apply Subtype.ext
  funext u
  have := congrFun hz u
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at this
  simp [this]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
