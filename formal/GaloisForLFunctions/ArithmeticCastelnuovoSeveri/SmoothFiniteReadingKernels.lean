import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WeilEnergyIsUnboundedAtEveryAperture

/-!
# Smooth unit-mass sources evade every finite reading

Infinite differentiability survives the finite-kernel construction and the
low-frequency exclusion argument. Thus the unbounded Weil Rayleigh witnesses
can be used as actual compact Meyer sources, retaining exact unit mass.
-/

open Complex MeasureTheory Set Filter Zeta23 GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate Real
noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Every finite-dimensional linear reading has a nonzero kernel at positive aperture. -/
theorem exists_nonzero_smooth_realTestAt_in_ker {r : ℝ} (hr : 0 < r)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, (f : realTests) ≠ 0 ∧ ContDiff ℝ (⊤ : ℕ∞) f.1.1 ∧ L f = 0 := by
  classical
  let N := Module.finrank ℝ V + 1
  have hnhd : Ioo (-(r / 2)) (r / 2) ∈ nhds (0 : ℝ) :=
    Ioo_mem_nhds (by linarith only [hr]) (by linarith only [hr])
  obtain ⟨g, hgs, hgc, hgd, -, hg0⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hnhd
  have hgne : g ≠ 0 := fun h => by simp [h] at hg0
  let s : Fin N → ℝ := fun i => -(r / 2) + i * (r / N)
  have hNpos : (0 : ℝ) < N := by dsimp [N]; positivity
  have hstep : 0 < r / N := div_pos hr hNpos
  have hsinj : Function.Injective s := by
    intro i j hij
    simp only [s, add_right_inj] at hij
    exact Fin.ext (by exact_mod_cast mul_right_cancel₀ hstep.ne' hij)
  have hs_mem : ∀ i, -(r / 2) ≤ s i ∧ s i ≤ r / 2 := by
    intro i
    have hi : (i : ℝ) ≤ N := by exact_mod_cast i.isLt.le
    have h1 : 0 ≤ (i : ℝ) * (r / N) := by positivity
    have h2 : (i : ℝ) * (r / N) ≤ r := by
      calc (i : ℝ) * (r / N) ≤ N * (r / N) :=
            mul_le_mul_of_nonneg_right hi hstep.le
        _ = r := by field_simp
    constructor <;> dsimp [s] <;> linarith only [h1, h2]
  let v : Fin N → ℝ → ℝ := fun i u => g (u - s i)
  have hvd : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (v i) :=
    fun _ => hgd.comp (contDiff_id.sub contDiff_const)
  have hvs : ∀ i, tsupport (v i) ⊆ Icc (-r) r := by
    intro i
    refine closure_minimal (fun u hu => ?_) isClosed_Icc
    have hu' : u - s i ∈ Ioo (-(r / 2)) (r / 2) := hgs (subset_tsupport g hu)
    obtain ⟨hs0, hs1⟩ := hs_mem i
    exact ⟨by linarith only [hu'.1, hs0], by linarith only [hu'.2, hs1]⟩
  have hvc : ∀ i, HasCompactSupport (v i) := fun i =>
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (hvs i)
  have hli : LinearIndependent ℝ v := linearIndependent_real_translate hsinj hgc hgne
  let vTest : Fin N → realTestsAt r := fun i => ⟨⟨v i, (hvd i).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2), hvc i⟩, hvs i⟩
  let B : (Fin N → ℝ) →ₗ[ℝ] realTestsAt r :=
    { toFun := fun c => ∑ i, c i • vTest i
      map_add' := fun c d => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum] }
  have hdim : Module.finrank ℝ V < Module.finrank ℝ (Fin N → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    dsimp [N]
    omega
  obtain ⟨c, hcker, hc0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := L.comp B) hdim)
  have hBc : ContDiff ℝ (⊤ : ℕ∞) (B c).1.1 := by
    have he : (∑ i, c i • v i) = fun x => ∑ i, c i • v i x := by
      funext x
      simp only [Finset.sum_apply, Pi.smul_apply]
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (∑ i, c i • v i) := by
      rw [he]
      exact ContDiff.sum fun i _ => (hvd i).const_smul (c i)
    simpa only [B, vTest, Submodule.coe_sum, Submodule.coe_smul] using hsum
  refine ⟨B c, ?_, hBc, hcker⟩
  intro h0
  have hf0 : ∑ i, c i • v i = 0 := by
    simpa [B, vTest] using congrArg Subtype.val h0
  exact hc0 (funext ((Fintype.linearIndependent_iff.mp hli) c hf0))

/-- The Weil Rayleigh quotient is unbounded in every finite-dimensional reading kernel. -/
theorem exists_smooth_realTestAt_in_ker_weilPair_gt_mul_integral_sq
    {r : ℝ} (hr : 0 < r) (M : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, ContDiff ℝ (⊤ : ℕ∞) f.1.1 ∧ 0 < ∫ u : ℝ, (f.1.1 u) ^ 2 ∧
      M * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 ∧ L f = 0 := by
  classical
  let ε := max M 0
  have hε : 0 ≤ ε := le_max_right _ _
  let T := horizonFreqEps r ε
  let G := lowGridOf T r
  let grid : Option G → ℂ := fun k => match k with
    | none => I / 2
    | some j => (((j : ℤ) : ℝ) * gridStepOf T r : ℝ)
  obtain ⟨f, hf0, hfsmooth, hker⟩ :=
    exists_nonzero_smooth_realTestAt_in_ker hr (L.prod (realTestAtFourierSamples r grid))
  have hvan : ∀ i, paperFT (cx f.1.1) (grid i) = 0 :=
    fun i => congrFun (congrArg Prod.snd hker) i
  have hmass := integral_sq_pos_of_realTest_ne_zero f.1 hf0
  refine ⟨f, hfsmooth, hmass, ?_, congrArg Prod.fst hker⟩
  have hFd := cx_contDiff f.1.2.1
  have hFc := cx_hasCompactSupport f.1.2.2
  have hFs : tsupport (cx f.1.1) ⊆ Icc (-r) r := by
    rw [tsupport_cx]
    exact f.2
  have hp : paperFT (cx f.1.1) (I / 2) = 0 := hvan none
  have hgrid : ∀ j ∈ G,
      paperFT (cx f.1.1) (((j : ℝ) * gridStepOf T r : ℝ) : ℂ) = 0 :=
    fun j hj => hvan (some ⟨j, hj⟩)
  have hW : (zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re = weilPair f.1.1 f.1.1 := by
    rw [weilPair, RHTower.zeta_W_eq_weilFullFunctional_mixed hFd hFc hFd hFc]
  have hnorm : (∫ u, ‖cx f.1.1 u‖ ^ 2) = ∫ u : ℝ, (f.1.1 u) ^ 2 := by
    congr 1
    funext u
    rw [cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hεW : ε * ∫ u : ℝ, (f.1.1 u) ^ 2 < weilPair f.1.1 f.1.1 := by
    by_contra hle
    have hle' : (zetaZeroConfig.W (cx f.1.1) (cx f.1.1)).re ≤ ε * ∫ u, ‖cx f.1.1 u‖ ^ 2 := by
      rw [hW, hnorm]
      exact le_of_not_gt hle
    have hlo := pi_mul_integral_le_of_re_W_le hε hFd hFs hp hle'
    have hhi := integral_band_le_of_lowGridOf (horizonFreqEps_nonneg r hε) hr.le
      hFd.continuous hFc hFs hgrid
    rw [hnorm] at hlo hhi
    have hπ : 1 < π := by linarith only [Real.pi_gt_three]
    have hstrict := mul_lt_mul_of_pos_right hπ hmass
    linarith only [hlo, hhi, hstrict]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_max_left M 0) hmass.le) hεW

/-- Fixing source mass to one does not bound Weil energy on any finite reading kernel. -/
theorem exists_smooth_realTestAt_unit_mass_in_ker_weilPair_gt {r : ℝ} (hr : 0 < r) (M : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : realTestsAt r →ₗ[ℝ] V) :
    ∃ f : realTestsAt r, ContDiff ℝ (⊤ : ℕ∞) f.1.1 ∧ (∫ u : ℝ, f.1.1 u ^ 2) = 1 ∧
      L f = 0 ∧ M < weilPair f.1.1 f.1.1 := by
  obtain ⟨f, hfd, hm, hW, hker⟩ := exists_smooth_realTestAt_in_ker_weilPair_gt_mul_integral_sq hr M L
  let m := ∫ u : ℝ, f.1.1 u ^ 2
  have hm' : 0 < m := hm
  let t := Real.sqrt (1 / m)
  have ht2 : t ^ 2 = 1 / m := Real.sq_sqrt (by positivity)
  have htpos : 0 < t ^ 2 := by rw [ht2]; positivity
  have htm : t ^ 2 * m = 1 := by rw [ht2]; field_simp [hm'.ne']
  refine ⟨t • f, hfd.const_smul t, ?_, ?_, ?_⟩
  · have he : (fun u : ℝ => ((t • f).1.1 u) ^ 2) =
        fun u : ℝ => t ^ 2 * f.1.1 u ^ 2 := by
      funext u
      change (t * f.1.1 u) ^ 2 = _
      ring
    rw [he, integral_const_mul]
    exact htm
  · rw [map_smul, hker, smul_zero]
  · have hscaled := mul_lt_mul_of_pos_left hW htpos
    have hleft : t ^ 2 * (M * m) = M := by
      calc
        _ = M * (t ^ 2 * m) := by ring
        _ = M := by rw [htm, mul_one]
    change t ^ 2 * (M * m) < t ^ 2 * weilPair f.1.1 f.1.1 at hscaled
    rw [hleft] at hscaled
    change M < weilPair (t • f.1.1) (t • f.1.1)
    rw [weilPair_smul_left, weilPair_comm f.1.1 (t • f.1.1), weilPair_smul_left]
    nlinarith only [hscaled]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_nonzero_smooth_realTestAt_in_ker
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_smooth_realTestAt_in_ker_weilPair_gt_mul_integral_sq
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_smooth_realTestAt_unit_mass_in_ker_weilPair_gt
