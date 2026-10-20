import GaloisForLFunctions.ArithmeticCriticalityTheory.PrimitiveHyperplaneCriticality

/-!
# The ground-state representation in an arbitrary gauge

Let `ω` be a gauge whose test coordinate `M = Φω` decays like `e^{−24|x|}`, whose two-sided
generator converges, and which satisfies a source equation `𝓛_D ω − Φ cosh(x/2) ω = Φ g`. For every
profile `u ∈ C²_c(ℝ)`, of any parity,

    markovEnergy(Φ(ω u)) = J_M(u) + ∫ u(x)² M(x) g(x) dx,

    J_M(u) = ∫ dm(t) ∫_ℝ M(x) M(x+t) (u(x) − u(x+t))² dx,

a **signed jump energy** with conductances `M(x)M(x+t)` (`markovEnergy_phiDoob_mul_eq_signedJump_add_source`).
The conductance is negative exactly on the jumps that cross a node of `M`. This contains the
two-sided representation of the shifted ground states (`M = m_a`, `g = 2 sinh(a/2) sinh(x/2)`,
the only node at the origin) and the definition of the Markov form (`M = Φ`, `g = −cosh(x/2)`). For
a **harmonic** gauge (`g = 0`) there is no potential at all:

    markovEnergy(Φ(ω u)) = J_M(u)          (`markovEnergy_phiDoob_mul_harmonic_eq_signedJump`):

on the tests it factors, the Markov form is a pure signed Dirichlet form, and every question of
sign is a question about the negative conductances across the nodes of `M`. Harmonic gauges exist in
abundance (the pole-free theta span), and none is positive on the half line.

Proof: the weak form `Q(Φz) = ∫ z(𝓛_D z − ρz)`, the Leibniz rule
`𝓛_D(ωu) = u 𝓛_D ω + Φ · Comm(M, u)`, and summation by parts of the commutator,
`∫ u M Comm(M, u) = J_M(u)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The signed jump of one shift, `M(x)M(x+t)(u(x) − u(x+t))²`. -/
def signedShiftJump (M u : ℝ → ℝ) (t x : ℝ) : ℝ := M x * M (x + t) * (u x - u (x + t)) ^ 2

/-- The signed jump energy `J_M(u) = ∫ dm(t) ∫_ℝ M(x)M(x+t)(u(x) − u(x+t))² dx`. -/
def signedJumpEnergy (M u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, signedShiftJump M u t x) +
    ∑' n : ℕ, vonMangoldtAtom n * ∫ x, signedShiftJump M u (Real.log n) x

/-! ### Summation by parts of the commutator -/

/-- `∫ u M (shift commutator) = ∫ M(x)M(x+t)(u(x) − u(x+t))²`. -/
theorem integral_mul_mul_shiftCommutator_eq {M u : ℝ → ℝ} (hM : Continuous M) (hu : Continuous u)
    (huc : HasCompactSupport u) (t : ℝ) :
    (∫ x, u x * M x * shiftCommutator M u t x) = ∫ x, signedShiftJump M u t x := by
  set f : ℝ → ℝ := fun x => u x * M x * M (x + t) * (u x - u (x + t)) with hf_def
  set g : ℝ → ℝ := fun y => u y * M y * M (y - t) * (u y - u (y - t)) with hg_def
  have hf : Integrable f := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.mul hM).mul (hM.comp (continuous_id.add continuous_const))).mul
        (hu.sub (hu.comp (continuous_id.add continuous_const)))
    · exact huc.mul_right.mul_right.mul_right
  have hg : Integrable g := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hu.mul hM).mul (hM.comp (continuous_id.sub continuous_const))).mul
        (hu.sub (hu.comp (continuous_id.sub continuous_const)))
    · exact huc.mul_right.mul_right.mul_right
  have h1 : (∫ x, u x * M x * shiftCommutator M u t x) = ∫ x, (f x + g x) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [shiftCommutator, hf_def, hg_def]
    ring
  have h2 : (∫ x, signedShiftJump M u t x) = ∫ x, (f x + g (x + t)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [signedShiftJump, hf_def, hg_def, add_sub_cancel_right]
    ring
  rw [h1, h2, integral_add hf hg, integral_add hf (hg.comp_add_right t),
    integral_add_right_eq_self g t]

/-! ### Bounds on the commutator for a general profile -/

theorem abs_shiftCommutator_le_of_bound {M u : ℝ → ℝ} {D : ℝ} (hD : ∀ x y, |u x - u y| ≤ D)
    (t x : ℝ) : |shiftCommutator M u t x| ≤ D * (|M (x + t)| + |M (x - t)|) := by
  unfold shiftCommutator
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD x x)
  nlinarith [mul_le_mul_of_nonneg_left (hD x (x + t)) (abs_nonneg (M (x + t))),
    mul_le_mul_of_nonneg_left (hD x (x - t)) (abs_nonneg (M (x - t)))]

theorem summable_atom_mul_shiftCommutator_of_bound {M u : ℝ → ℝ} {C D : ℝ} (hC0 : 0 ≤ C)
    (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|))) (hD : ∀ x y, |u x - u y| ≤ D) (x : ℝ) :
    Summable fun n : ℕ => vonMangoldtAtom n * shiftCommutator M u (Real.log n) x := by
  have hD0 : 0 ≤ D := le_trans (abs_nonneg _) (hD x x)
  refine Summable.of_norm_bounded (summable_atom_mul_exp_neg_eight_log.mul_left
    (2 * C * D * Real.exp (8 * |x|))) fun n => ?_
  have hΛ := vonMangoldtAtom_nonneg n
  have hb := abs_shiftCommutator_le_of_bound (M := M) hD (Real.log n) x
  have ep : |M (x + Real.log n)| ≤ C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
    (hM _).trans (mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (by
      linarith [abs_nonneg (x + Real.log n)])).trans (exp_neg_eight_mul_abs_add_log_le x n)) hC0)
  have em : |M (x - Real.log n)| ≤ C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) :=
    (hM _).trans (mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (by
      linarith [abs_nonneg (x - Real.log n)])).trans (exp_neg_eight_mul_abs_sub_log_le x n)) hC0)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hΛ]
  calc vonMangoldtAtom n * |shiftCommutator M u (Real.log n) x|
      ≤ vonMangoldtAtom n * (D * (C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))) +
          C * (Real.exp (8 * |x|) * Real.exp (-(8 * Real.log n))))) :=
        mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left (add_le_add ep em) hD0)) hΛ
    _ = _ := by ring

/-! ### The commutator pairing is the signed jump energy -/

theorem continuous_shiftCommutator_uncurry {M u : ℝ → ℝ} (hM : Continuous M) (hu : Continuous u) :
    Continuous fun p : ℝ × ℝ => shiftCommutator M u p.1 p.2 := by
  unfold shiftCommutator
  exact ((hM.comp (continuous_snd.add continuous_fst)).mul
    ((hu.comp continuous_snd).sub (hu.comp (continuous_snd.add continuous_fst)))).add
    ((hM.comp (continuous_snd.sub continuous_fst)).mul
      ((hu.comp continuous_snd).sub (hu.comp (continuous_snd.sub continuous_fst))))

/-- **Summation by parts of the commutator.** `∫ u M Comm(M, u) = J_M(u)`. -/
theorem integral_mul_mul_plateauCommutator_eq_signedJumpEnergy {M u : ℝ → ℝ} {C : ℝ}
    (hMc : Continuous M) (hC0 : 0 ≤ C) (hM : ∀ y, |M y| ≤ C * Real.exp (-(24 * |y|)))
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    (∫ x, u x * M x * plateauCommutator M u x) = signedJumpEnergy M u := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  obtain ⟨Z, hZ⟩ := huc.exists_bound_of_continuous hu.continuous
  have hZ' : ∀ x, |u x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ' 0)
  have hD : ∀ x y, |u x - u y| ≤ 2 * Z := fun x y => by
    have := abs_sub (u x) (u y)
    linarith [hZ' x, hZ' y]
  obtain ⟨R, -, hsupp⟩ := exists_support_radius huc
  have hMb : ∀ y, |M y| ≤ C := fun y => by
    have h2 : Real.exp (-(24 * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])
    nlinarith [hM y, mul_le_mul_of_nonneg_left h2 hC0]
  have hucont := hu.continuous
  have hui : Integrable fun x => |u x| := (hucont.integrable_of_hasCompactSupport huc).abs
  -- archimedean Fubini
  have hprod : Integrable (Function.uncurry fun t x =>
      archLevyDensity t * (u x * M x * shiftCommutator M u t x))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hmaj : Integrable (fun p : ℝ × ℝ =>
        (archLevyDensity p.1 * p.1) * ((C * (2 * C * Λ)) * |u p.2|))
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
      integrableOn_archLevyDensity_mul_id.mul_prod (hui.const_mul _)
    refine hmaj.mono' ?_ ?_
    · exact ((measurable_archLevyDensity.comp measurable_fst).mul
        (((hucont.comp continuous_snd).mul (hMc.comp continuous_snd)).mul
          (continuous_shiftCommutator_uncurry hMc hucont)).measurable).aestronglyMeasurable
    · rw [Measure.restrict_prod_eq_prod_univ]
      refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
      have ht : 0 < p.1 := hp.1
      have hA := archLevyDensity_pos ht
      have hb := abs_shiftCommutator_le_lipschitz hMb hΛ ht.le p.2
      show ‖archLevyDensity p.1 * (u p.2 * M p.2 * shiftCommutator M u p.1 p.2)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hA, abs_mul, abs_mul]
      have h1 := hMb p.2
      have hu0 := abs_nonneg (u p.2)
      calc archLevyDensity p.1 * (|u p.2| * |M p.2| * |shiftCommutator M u p.1 p.2|)
          ≤ archLevyDensity p.1 * (|u p.2| * C * (2 * C * Λ * p.1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA.le
            exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hu0) hb (abs_nonneg _)
              (mul_nonneg hu0 hC0)
        _ = _ := by ring
  have harch : (∫ x, u x * M x * ∫ t in Ioi (0 : ℝ), archLevyDensity t * shiftCommutator M u t x) =
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, signedShiftJump M u t x := by
    have h1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x, signedShiftJump M u t x) =
        ∫ t in Ioi (0 : ℝ), ∫ x, archLevyDensity t * (u x * M x * shiftCommutator M u t x) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [integral_const_mul, integral_mul_mul_shiftCommutator_eq hMc hucont huc]
    rw [h1, integral_integral_swap hprod]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  -- prime exchange
  set F : ℕ → ℝ → ℝ := fun n x => vonMangoldtAtom n * (u x * M x * shiftCommutator M u (Real.log n) x)
    with hF_def
  have hFint : ∀ n, Integrable (F n) := fun n => by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact continuous_const.mul ((hucont.mul hMc).mul
        ((continuous_shiftCommutator_uncurry hMc hucont).comp
          (continuous_const.prodMk continuous_id)))
    · exact (huc.mul_right.mul_right).mul_left
  set K := 2 * Z * C * (2 * C * Real.exp (8 * R))
  have hbound : ∀ n x, |F n x| ≤ K * (vonMangoldtAtom n * Real.exp (-(8 * Real.log n))) * |u x| :=
    fun n x => by
      have hΛn := vonMangoldtAtom_nonneg n
      by_cases hx : |x| ≤ R
      · have hb := abs_shiftCommutator_le_of_bound (M := M) hD (Real.log n) x
        have ep : |M (x + Real.log n)| ≤ C * (Real.exp (8 * R) * Real.exp (-(8 * Real.log n))) :=
          (hM _).trans (mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (by
            linarith [abs_nonneg (x + Real.log n)])).trans ((exp_neg_eight_mul_abs_add_log_le x n).trans
              (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le)))
            hC0)
        have em : |M (x - Real.log n)| ≤ C * (Real.exp (8 * R) * Real.exp (-(8 * Real.log n))) :=
          (hM _).trans (mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr (by
            linarith [abs_nonneg (x - Real.log n)])).trans ((exp_neg_eight_mul_abs_sub_log_le x n).trans
              (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le)))
            hC0)
        have hsc : |shiftCommutator M u (Real.log n) x| ≤
            2 * Z * (2 * C * (Real.exp (8 * R) * Real.exp (-(8 * Real.log n)))) := by
          refine hb.trans ?_
          have := add_le_add ep em
          nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * Z)]
        simp only [hF_def]
        rw [abs_mul, abs_of_nonneg hΛn, abs_mul, abs_mul]
        calc vonMangoldtAtom n * (|u x| * |M x| * |shiftCommutator M u (Real.log n) x|)
            ≤ vonMangoldtAtom n * (|u x| * C *
                (2 * Z * (2 * C * (Real.exp (8 * R) * Real.exp (-(8 * Real.log n)))))) := by
              refine mul_le_mul_of_nonneg_left ?_ hΛn
              exact mul_le_mul (mul_le_mul_of_nonneg_left (hMb x) (abs_nonneg _)) hsc
                (abs_nonneg _) (mul_nonneg (abs_nonneg _) hC0)
          _ = _ := by ring
      · simp only [hF_def]
        rw [hsupp x (not_le.mp hx)]
        simp
  have hsum : Summable fun n => ∫ x, ‖F n x‖ := by
    have hmaj : Summable fun n : ℕ =>
        K * (vonMangoldtAtom n * Real.exp (-(8 * Real.log n))) * ∫ x, |u x| :=
      (summable_atom_mul_exp_neg_eight_log.mul_left K).mul_right _
    refine hmaj.of_nonneg_of_le (fun n => integral_nonneg fun x => norm_nonneg _) fun n => ?_
    rw [← integral_const_mul]
    exact integral_mono (hFint n).norm (hui.const_mul _) fun x => by
      simpa [Real.norm_eq_abs] using hbound n x
  have hprime : (∫ x, u x * M x * ∑' n : ℕ, vonMangoldtAtom n * shiftCommutator M u (Real.log n) x) =
      ∑' n : ℕ, vonMangoldtAtom n * ∫ x, signedShiftJump M u (Real.log n) x := by
    have h1 : (∑' n : ℕ, vonMangoldtAtom n * ∫ x, signedShiftJump M u (Real.log n) x) =
        ∑' n : ℕ, ∫ x, F n x := by
      refine tsum_congr fun n => ?_
      rw [← integral_mul_mul_shiftCommutator_eq hMc hucont huc, ← integral_const_mul]
    rw [h1, integral_tsum_of_summable_integral_norm hFint hsum]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF_def]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  -- assembly
  have hAi : Integrable fun x => u x * M x * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
      shiftCommutator M u t x := by
    have h := hprod.integral_prod_right
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  have hPi : Integrable fun x => u x * M x * ∑' n : ℕ, vonMangoldtAtom n *
      shiftCommutator M u (Real.log n) x := by
    have hmeas : AEStronglyMeasurable (fun x => u x * M x * ∑' n : ℕ, vonMangoldtAtom n *
        shiftCommutator M u (Real.log n) x) volume := by
      refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => u x * M x *
        ∑ n ∈ Finset.range N, vonMangoldtAtom n * shiftCommutator M u (Real.log n) x)
        atTop (fun N => ?_) (Eventually.of_forall fun x => ?_)
      · exact ((hucont.mul hMc).mul (continuous_finsetSum _ fun n _ =>
          continuous_const.mul ((continuous_shiftCommutator_uncurry hMc hucont).comp
            (continuous_const.prodMk continuous_id)))).aestronglyMeasurable
      · exact ((summable_atom_mul_shiftCommutator_of_bound hC0 hM hD x).hasSum.tendsto_sum_nat).const_mul _
    set S := ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(8 * Real.log n))
    refine (hui.const_mul (K * S)).mono' hmeas (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, ← tsum_mul_left]
    have hB : Summable fun n : ℕ => K * (vonMangoldtAtom n * Real.exp (-(8 * Real.log n))) * |u x| :=
      (summable_atom_mul_exp_neg_eight_log.mul_left K).mul_right _
    have hnorm : Summable fun n : ℕ => ‖u x * M x * (vonMangoldtAtom n *
        shiftCommutator M u (Real.log n) x)‖ :=
      hB.of_nonneg_of_le (fun n => norm_nonneg _) fun n => by
        rw [Real.norm_eq_abs, show u x * M x * (vonMangoldtAtom n * shiftCommutator M u
          (Real.log n) x) = F n x by simp only [hF_def]; ring]
        exact hbound n x
    calc |∑' n : ℕ, u x * M x * (vonMangoldtAtom n * shiftCommutator M u (Real.log n) x)|
        ≤ ∑' n : ℕ, ‖u x * M x * (vonMangoldtAtom n * shiftCommutator M u (Real.log n) x)‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : ℕ, K * (vonMangoldtAtom n * Real.exp (-(8 * Real.log n))) * |u x| :=
          Summable.tsum_le_tsum (fun n => by
            rw [Real.norm_eq_abs, show u x * M x * (vonMangoldtAtom n * shiftCommutator M u
              (Real.log n) x) = F n x by simp only [hF_def]; ring]
            exact hbound n x) hnorm hB
      _ = K * S * |u x| := by rw [tsum_mul_right, tsum_mul_left]
  unfold plateauCommutator signedJumpEnergy
  rw [← harch, ← hprime, ← integral_add hAi hPi]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  ring

/-! ### The representation -/

/-- **The ground-state representation in an arbitrary gauge.** If `M = Φω` decays like
`e^{−24|·|}`, the generator of `ω` converges, and `𝓛_D ω − Φ cosh(x/2) ω = Φ g`, then for every
`u ∈ C²_c(ℝ)`: `markovEnergy(Φ(ω u)) = J_M(u) + ∫ u² M g`. -/
theorem markovEnergy_phiDoob_mul_eq_signedJump_add_source {ω g u : ℝ → ℝ} {C : ℝ}
    (hω : ContDiff ℝ 2 ω) (hC0 : 0 ≤ C)
    (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * g x) (hg : Continuous g)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) =
      signedJumpEnergy (fun y => riemannKernelReal y * ω y) u +
        ∫ x, u x ^ 2 * (riemannKernelReal x * ω x) * g x := by
  set M : ℝ → ℝ := fun y => riemannKernelReal y * ω y with hM_def
  have hMc : Continuous M := continuous_riemannKernelReal.mul hω.continuous
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_lipschitz_bound_of_compactSupport (hu.of_le (by norm_num)) huc
  obtain ⟨Z, hZ⟩ := huc.exists_bound_of_continuous hu.continuous
  have hZ' : ∀ x, |u x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  have hD : ∀ x y, |u x - u y| ≤ 2 * Z := fun x y => by
    have := abs_sub (u x) (u y)
    linarith [hZ' x, hZ' y]
  have hMb : ∀ y, |M y| ≤ C := fun y => by
    have h2 : Real.exp (-(24 * |y|)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])
    nlinarith [hM y, mul_le_mul_of_nonneg_left h2 hC0]
  set z : ℝ → ℝ := fun y => ω y * u y with hz_def
  have hz : ContDiff ℝ 2 z := hω.mul hu
  have hzc : HasCompactSupport z := huc.mul_left
  -- pointwise splitting
  have hpt : ∀ x, z x * (twoSidedGenerator z x - riemannKernelReal x * Real.cosh (x / 2) * z x) =
      u x ^ 2 * M x * g x + u x * M x * plateauCommutator M u x := fun x => by
    have hL := twoSidedGenerator_mul (hA x) (hP x)
      (integrableOn_archLevy_shiftCommutator hMc hu.continuous hMb hΛ x)
      (summable_atom_mul_shiftCommutator_of_bound hC0 hM hD x)
    simp only [hz_def]
    rw [hL]
    linear_combination (ω x * u x ^ 2) * hsrc x
  have hPot : Integrable fun x => z x * (riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hzc.mul_right
    exact hz.continuous.mul ((continuous_riemannKernelReal.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul hz.continuous)
  have hI : Integrable fun x => z x * (twoSidedGenerator z x -
      riemannKernelReal x * Real.cosh (x / 2) * z x) := by
    refine (((integrable_mul_archTwoSidedGenerator hz hzc).add
      (integrable_mul_primeTwoSidedGenerator hz hzc)).sub hPot).congr
      (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, twoSidedGenerator_eq_arch_add_prime]
    ring
  have hS : Integrable fun x => u x ^ 2 * M x * g x := by
    refine Continuous.integrable_of_hasCompactSupport (((hu.continuous.pow 2).mul hMc).mul hg) ?_
    exact ((hasCompactSupport_sq huc).mul_right).mul_right
  have hC' : Integrable fun x => u x * M x * plateauCommutator M u x := by
    refine (hI.sub hS).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    rw [hpt x]
    ring
  rw [markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential hz hzc]
  rw [show (fun x => z x * (twoSidedGenerator z x - riemannKernelReal x * Real.cosh (x / 2) * z x))
    = fun x => u x ^ 2 * M x * g x + u x * M x * plateauCommutator M u x from funext hpt,
    integral_add hS hC', integral_mul_mul_plateauCommutator_eq_signedJumpEnergy hMc hC0 hM hu huc]
  ring

/-- **Harmonic gauges carry no potential.** If `𝓛_D ω = Φ cosh(x/2) ω`, then
`markovEnergy(Φ(ω u)) = J_M(u)` for every `u ∈ C²_c(ℝ)`. -/
theorem markovEnergy_phiDoob_mul_harmonic_eq_signedJump {ω u : ℝ → ℝ} {C : ℝ}
    (hω : ContDiff ℝ 2 ω) (hC0 : 0 ≤ C)
    (hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)))
    (hA : ∀ x, IntegrableOn (fun t => archLevyDensity t * twoSidedShiftGenerator ω t x) (Ioi 0))
    (hP : ∀ x, Summable fun n : ℕ => vonMangoldtAtom n * twoSidedShiftGenerator ω (Real.log n) x)
    (hharm : ∀ x, twoSidedGenerator ω x = riemannKernelReal x * Real.cosh (x / 2) * ω x)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) =
      signedJumpEnergy (fun y => riemannKernelReal y * ω y) u := by
  rw [markovEnergy_phiDoob_mul_eq_signedJump_add_source (g := fun _ => 0) hω hC0 hM hA hP
    (fun x => by rw [hharm x]; ring) continuous_const hu huc]
  simp

/-- **Instance: finite combinations of translates.** For `ω = Σ α_j τ_{b_j}`,
`markovEnergy(Φ(ω u)) = J_M(u) − ∫ u² M (A cosh(x/2) − B sinh(x/2))`. -/
theorem markovEnergy_phiDoob_translateSpan_mul_eq {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => translateSpan s α b y * u y) x : ℂ)) =
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u +
        ∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x) * translateSource s α b x := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_riemannKernelReal_mul_translateSpan_le s α b
  exact markovEnergy_phiDoob_mul_eq_signedJump_add_source (contDiff_translateSpan s α b) hC0 hC
    (integrableOn_archLevy_twoSidedShiftGenerator_translateSpan s α b)
    (summable_atom_twoSidedShiftGenerator_translateSpan s α b)
    (twoSidedGenerator_translateSpan_sub_potential s α b) (continuous_translateSource s α b) hu huc

/-- **Instance: harmonic combinations of translates** (`A = B = 0`): a pure signed jump energy. -/
theorem markovEnergy_phiDoob_translateSpan_mul_eq_signedJump_of_harmonic {ι : Type*}
    {s : Finset ι} {α b : ι → ℝ} (hA : translateCoshCoefficient s α b = 0)
    (hB : translateSinhCoefficient s α b = 0) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) :
    markovEnergy (fun x => (phiDoobTest (fun y => translateSpan s α b y * u y) x : ℂ)) =
      signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u := by
  rw [markovEnergy_phiDoob_translateSpan_mul_eq s α b hu huc]
  have h0 : ∀ x, translateSource s α b x = 0 := fun x => by
    unfold translateSource
    rw [hA, hB]
    ring
  simp [h0]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
