import GaloisForLFunctions.ArithmeticCriticalityTheory.ZeroFormGaugeInvariance

/-!
# The archimedean place is Z-type: every obstruction to the variation inequality is prime

Split the energies of the two-sided representation into archimedean and prime parts,
`S = S_arch + S_prime`, `D = D_arch + D_prime`. In the pair coordinates `(x, y)` of one jump, the
same-side jumps sit on the lines `y − x = t` and the reflected jumps on the anti-diagonals
`x + y = t`; the archimedean density `ω_arch(t) = e^{−t/2}/(1 − e^{−2t})` charges both, and it is
decreasing. Folding the reflected collar at its midpoint and moving every jump to the same pair of
points gives the two exact representations

    D_arch(ω_a, u) = 2 ∫_{x>0} ∫_{s>0} ω_arch(s + 2x) J_s(x) ds dx,
    S_arch(ω_a, u) =   ∫_{x>0} ∫_{s>0} ω_arch(s) J_s(x) ds dx,

with `J_s(x) = Φ(x)Φ(x+s) ω_a(x) ω_a(x+s) (u(x) − u(x+s))² ≥ 0` the same-side jump
(`archReflectedDifferenceEnergy_eq`, `archSameSideEnergy_eq`). Since `ω_arch(s + 2x) ≤ ω_arch(s)`,

    D_arch(ω_a, u) ≤ 2 S_arch(ω_a, u)       for every shift and every profile

(`archReflectedDifferenceEnergy_le_two_mul_archSameSideEnergy`). The variation inequality holds at
the archimedean place with no source at all. Every violation of the pole-free variation inequality,
hence every failure of RH, is carried by the prime anti-diagonal atoms `x + y = log n`, at which
`Λ(n) n^{−1/2}` is not dominated by the same-side atoms at `|x − y| = log m`: the odd arithmetic
operator is non-Z-type exactly because the prime jump measure is not monotone.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The archimedean same-side energy `∫_{t>0} ω(t) ∫_{x>0} J_t(x) dx dt`. -/
def archSameSideEnergy (ω u : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x

/-- The archimedean reflected difference energy `∫_{t>0} ω(t) ∫_0^t R_t(x) dx dt`. -/
def archReflectedDifferenceEnergy (ω u : ℝ → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump ω u t x

theorem reflectedDifferenceJump_comm (ω u : ℝ → ℝ) (t x : ℝ) :
    reflectedDifferenceJump ω u t (t - x) = reflectedDifferenceJump ω u t x := by
  unfold reflectedDifferenceJump
  rw [sub_sub_cancel]
  ring

theorem reflectedDifferenceJump_add_two_mul (ω u : ℝ → ℝ) (s x : ℝ) :
    reflectedDifferenceJump ω u (s + 2 * x) x = sameSideGroundJump ω u s x := by
  unfold reflectedDifferenceJump sameSideGroundJump
  rw [show s + 2 * x - x = x + s by ring]

/-- **Midpoint folding of the reflected collar.**
`∫_0^t R_t(x) dx = 2 ∫_0^{t/2} R_t(x) dx`, `R_t` being symmetric under `x ↦ t − x`. -/
theorem integral_Ioo_reflectedDifferenceJump_eq_two_mul_half {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump ω u t x) =
      2 * ∫ x in Ioo (0 : ℝ) (t / 2), reflectedDifferenceJump ω u t x := by
  have hc : Continuous fun x => reflectedDifferenceJump ω u t x :=
    (continuous_reflectedDifferenceJump_uncurry hω hu).comp (continuous_const.prodMk continuous_id)
  have hI : IntegrableOn (fun x => reflectedDifferenceJump ω u t x) (Ioo 0 t) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hsplit : (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump ω u t x) =
      (∫ x in Ioc (0 : ℝ) (t / 2), reflectedDifferenceJump ω u t x) +
        ∫ x in Ioo (t / 2) t, reflectedDifferenceJump ω u t x := by
    have hd : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioo (t / 2) t) :=
      Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
    have h1 : IntegrableOn (fun x => reflectedDifferenceJump ω u t x) (Ioc 0 (t / 2)) :=
      hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have h2 : IntegrableOn (fun x => reflectedDifferenceJump ω u t x) (Ioo (t / 2) t) :=
      hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
    rw [← setIntegral_union hd measurableSet_Ioo h1 h2,
      Ioc_union_Ioo_eq_Ioo (by linarith) (by linarith)]
  rw [hsplit, integral_Ioc_eq_integral_Ioo, setIntegral_Ioo_reflect_midpoint]
  simp_rw [reflectedDifferenceJump_comm]
  ring

theorem setIntegral_Ioi_translate (g : ℝ → ℝ) (c : ℝ) :
    (∫ t in Ioi c, g t) = ∫ s in Ioi (0 : ℝ), g (s + c) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun t => (Ioi c).indicator g t) c]
  congr 1
  funext s
  simp only [Set.indicator, Set.mem_Ioi]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; linarith)

/-! ### Fubini for the two archimedean energies -/

section ShiftedGroundState

variable {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
include ha hu huc

theorem integrable_archLevy_mul_sameSideGroundJump_prod :
    Integrable (Function.uncurry fun t x =>
      archLevyDensity t * sameSideGroundJump (shiftedGroundState a) u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu huc
  have hS := integrableOn_archLevy_mul_sameSideIntegral hωc hu.continuous hpos hadm
  have hmeas : Measurable (Function.uncurry fun t x =>
      archLevyDensity t * sameSideGroundJump (shiftedGroundState a) u t x) :=
    (measurable_archLevyDensity.comp measurable_fst).mul
      (continuous_sameSideGroundJump_uncurry hωc hu.continuous).measurable
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
    have hJ : IntegrableOn (sameSideGroundJump (shiftedGroundState a) u t) (Ioi 0) := by
      have : sameSideGroundJump (shiftedGroundState a) u t = fun x =>
          (riemannKernelReal x * riemannKernelReal (x + t) * shiftedGroundState a x *
            shiftedGroundState a (x + t)) * (u x - u (x + t)) ^ 2 := by
        funext x
        simp only [sameSideGroundJump]
      rw [this]
      have hΦ := continuous_riemannKernelReal
      exact integrableOn_continuous_mul_sq
        (((hΦ.mul (hΦ.comp (continuous_id.add continuous_const))).mul hωc).mul
          (hωc.comp (continuous_id.add continuous_const)))
        (hu.continuous.sub (continuous_shift hu.continuous t))
        (huc.sub (hasCompactSupport_shift huc t)) _
    show Integrable (fun x => archLevyDensity t * sameSideGroundJump (shiftedGroundState a) u t x)
      (volume.restrict (Ioi 0))
    exact hJ.const_mul _
  · refine hS.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Function.uncurry_apply_pair]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le
      (sameSideGroundJump_nonneg hpos (mem_Ioi.mp ht).le hx))]

omit hu huc in
theorem reflectedDifferenceJump_shiftedGroundState_nonneg {t x : ℝ} (hx : 0 < x) (hxt : x < t) :
    0 ≤ reflectedDifferenceJump (shiftedGroundState a) u t x := by
  unfold reflectedDifferenceJump
  have h1 := riemannKernelReal_pos x
  have h2 := riemannKernelReal_pos (t - x)
  have h3 := shiftedGroundState_pos ha hx
  have h4 := shiftedGroundState_pos ha (show 0 < t - x by linarith)
  positivity

/-- The folded reflected integrand `ω(t) 1_{0<x<t/2} R_t(x)` on `(0,∞)²`. -/
def foldedReflectedIntegrand (a : ℝ) (u : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  archLevyDensity p.1 *
    ({q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2}.indicator
      (fun q => reflectedDifferenceJump (shiftedGroundState a) u q.1 q.2) p)

omit ha hu huc in
theorem foldedReflectedIntegrand_apply (t x : ℝ) :
    foldedReflectedIntegrand a u (t, x) = archLevyDensity t *
      (Ioo (0 : ℝ) (t / 2)).indicator (fun y => reflectedDifferenceJump (shiftedGroundState a) u t y)
        x := by
  unfold foldedReflectedIntegrand
  simp only [Set.indicator_apply, mem_setOf_eq, mem_Ioo]

theorem integrable_foldedReflectedIntegrand :
    Integrable (foldedReflectedIntegrand a u)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hD := integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hu huc
  have hset : MeasurableSet {q : ℝ × ℝ | 0 < q.2 ∧ q.2 < q.1 / 2} := by
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (measurable_fst.div_const 2))
  have hmeas : Measurable (foldedReflectedIntegrand a u) :=
    (measurable_archLevyDensity.comp measurable_fst).mul
      ((continuous_reflectedDifferenceJump_uncurry hωc hu.continuous).measurable.indicator hset)
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
    have hc : Continuous fun y => reflectedDifferenceJump (shiftedGroundState a) u t y :=
      (continuous_reflectedDifferenceJump_uncurry hωc hu.continuous).comp
        (continuous_const.prodMk continuous_id)
    have hI : Integrable ((Ioo (0 : ℝ) (t / 2)).indicator
        fun y => reflectedDifferenceJump (shiftedGroundState a) u t y) :=
      (hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo
    refine (hI.integrableOn.const_mul (archLevyDensity t)).congr ?_
    exact Eventually.of_forall fun x => (foldedReflectedIntegrand_apply t x).symm
  · have hD2 : IntegrableOn (fun t => 1 / 2 * (archLevyDensity t * ∫ x in Ioo (0 : ℝ) t,
        reflectedDifferenceJump (shiftedGroundState a) u t x)) (Ioi 0) := hD.const_mul _
    refine hD2.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : 0 < t := ht
    simp only
    rw [integral_Ioo_reflectedDifferenceJump_eq_two_mul_half hωc hu.continuous ht0]
    have hEq : (∫ x in Ioi (0 : ℝ), ‖foldedReflectedIntegrand a u (t, x)‖) =
        archLevyDensity t * ∫ x in Ioo (0 : ℝ) (t / 2),
          reflectedDifferenceJump (shiftedGroundState a) u t x := by
      have h1 : (∫ x in Ioi (0 : ℝ), ‖foldedReflectedIntegrand a u (t, x)‖) =
          ∫ x in Ioi (0 : ℝ), archLevyDensity t * (Ioo (0 : ℝ) (t / 2)).indicator
            (fun y => reflectedDifferenceJump (shiftedGroundState a) u t y) x := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [foldedReflectedIntegrand_apply, Real.norm_of_nonneg]
        refine mul_nonneg (archLevyDensity_pos ht0).le ?_
        simp only [Set.indicator_apply, mem_Ioo]
        split_ifs with h
        · exact reflectedDifferenceJump_shiftedGroundState_nonneg ha h.1 (by linarith [h.2])
        · exact le_rfl
      rw [h1, integral_const_mul, setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.mpr (Ioo_subset_Ioi_self)]
    rw [hEq]
    ring

omit ha hu huc in
/-- The folded reflected integrand at fixed `x > 0`, as a shift integral. -/
theorem integral_foldedReflectedIntegrand_eq {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), foldedReflectedIntegrand a u (t, x)) =
      ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
        sameSideGroundJump (shiftedGroundState a) u s x := by
  have h1 : (∫ t in Ioi (0 : ℝ), foldedReflectedIntegrand a u (t, x)) =
      ∫ t in Ioi (2 * x), archLevyDensity t * reflectedDifferenceJump (shiftedGroundState a) u t x := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    congr 1
    funext t
    simp only [Set.indicator_apply, mem_Ioi, foldedReflectedIntegrand_apply, mem_Ioo]
    by_cases h : 2 * x < t
    · rw [if_pos (by linarith), if_pos ⟨hx, by linarith⟩, if_pos h]
    · rw [if_neg h]
      by_cases h' : 0 < t
      · rw [if_pos h', if_neg (fun hh => h (by linarith [hh.2])), mul_zero]
      · rw [if_neg h']
  rw [h1, setIntegral_Ioi_translate]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [reflectedDifferenceJump_add_two_mul]

/-- `D_arch(ω_a, u) = 2 ∫_{x>0} ∫_{s>0} ω(s + 2x) J_s(x) ds dx`. -/
theorem archReflectedDifferenceEnergy_eq :
    archReflectedDifferenceEnergy (shiftedGroundState a) u =
      2 * ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
        sameSideGroundJump (shiftedGroundState a) u s x := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hID := integrable_foldedReflectedIntegrand ha hu huc
  unfold archReflectedDifferenceEnergy
  have h1 : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), archLevyDensity (s + 2 * x) *
      sameSideGroundJump (shiftedGroundState a) u s x) =
      ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), foldedReflectedIntegrand a u (t, x) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      (integral_foldedReflectedIntegrand_eq (mem_Ioi.mp hx)).symm
  rw [h1, ← integral_integral_swap (f := fun t x => foldedReflectedIntegrand a u (t, x)) hID,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [integral_Ioo_reflectedDifferenceJump_eq_two_mul_half hωc hu.continuous (mem_Ioi.mp ht)]
  have : (∫ x in Ioi (0 : ℝ), foldedReflectedIntegrand a u (t, x)) =
      archLevyDensity t * ∫ x in Ioo (0 : ℝ) (t / 2),
        reflectedDifferenceJump (shiftedGroundState a) u t x := by
    simp_rw [foldedReflectedIntegrand_apply]
    rw [integral_const_mul, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self]
  rw [this]
  ring

/-- `S_arch(ω_a, u) = ∫_{x>0} ∫_{s>0} ω(s) J_s(x) ds dx`. -/
theorem archSameSideEnergy_eq :
    archSameSideEnergy (shiftedGroundState a) u =
      ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ),
        archLevyDensity s * sameSideGroundJump (shiftedGroundState a) u s x := by
  have hIS := integrable_archLevy_mul_sameSideGroundJump_prod ha hu huc
  unfold archSameSideEnergy
  rw [← integral_integral_swap (f := fun t x =>
    archLevyDensity t * sameSideGroundJump (shiftedGroundState a) u t x) hIS]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [integral_const_mul]

/-- **The archimedean place is Z-type.** `D_arch(ω_a, u) ≤ 2 S_arch(ω_a, u)`. -/
theorem archReflectedDifferenceEnergy_le_two_mul_archSameSideEnergy :
    archReflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * archSameSideEnergy (shiftedGroundState a) u := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hIS := integrable_archLevy_mul_sameSideGroundJump_prod ha hu huc
  rw [archReflectedDifferenceEnergy_eq ha hu huc, archSameSideEnergy_eq ha hu huc]
  refine mul_le_mul_of_nonneg_left ?_ zero_le_two
  -- compare the inner integrals pointwise in `x`
  have hsec := hIS.prod_left_ae
  have hout := hIS.integral_prod_right
  refine integral_mono_of_nonneg ?_ hout ?_
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    exact setIntegral_nonneg measurableSet_Ioi fun s hs => mul_nonneg
      (archLevyDensity_pos (by linarith [mem_Ioi.mp hs, mem_Ioi.mp hx])).le
      (sameSideGroundJump_nonneg hpos (mem_Ioi.mp hs).le hx)
  · filter_upwards [hsec, ae_restrict_mem measurableSet_Ioi] with x hx hx0
    have hx0' : 0 < x := hx0
    refine integral_mono_of_nonneg ?_ hx ?_
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => mul_nonneg
        (archLevyDensity_pos (by linarith [mem_Ioi.mp hs])).le
        (sameSideGroundJump_nonneg hpos (mem_Ioi.mp hs).le hx0')
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
      have hs0 : 0 < s := hs
      show archLevyDensity (s + 2 * x) * sameSideGroundJump (shiftedGroundState a) u s x ≤
        archLevyDensity s * sameSideGroundJump (shiftedGroundState a) u s x
      exact mul_le_mul_of_nonneg_right
        (strictAntiOn_archLevyDensity.antitoneOn hs0 (show (0 : ℝ) < s + 2 * x by linarith)
          (by linarith))
        (sameSideGroundJump_nonneg hpos hs0.le hx0')

end ShiftedGroundState

/-! ### Every obstruction is prime -/

/-- The prime same-side energy `Σ Λ(n) n^{−1/2} ∫_{x>0} J_{log n}(x) dx`. -/
def primeSameSideEnergy (ω u : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u (Real.log n) x

/-- The prime reflected difference energy `Σ Λ(n) n^{−1/2} ∫_0^{log n} R_{log n}(x) dx`. -/
def primeReflectedDifferenceEnergy (ω u : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldtAtom n *
    ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedDifferenceJump ω u (Real.log n) x

theorem sameSideEnergy_eq_arch_add_prime (ω u : ℝ → ℝ) :
    sameSideEnergy ω u = archSameSideEnergy ω u + primeSameSideEnergy ω u := rfl

theorem reflectedDifferenceEnergy_eq_arch_add_prime (ω u : ℝ → ℝ) :
    reflectedDifferenceEnergy ω u =
      archReflectedDifferenceEnergy ω u + primeReflectedDifferenceEnergy ω u := rfl

/-- **RH is a statement about the prime anti-diagonals.** For every shift `a > 0`, RH holds iff for
every even `u ∈ C²_c(ℝ)`
`D_prime(u) ≤ (2 S_arch(u) − D_arch(u)) + 2 S_prime(u) + V_a(u)`, where the archimedean surplus
`2 S_arch − D_arch` is nonnegative for every profile. -/
theorem riemannHypothesis_iff_forall_prime_variationInequality {a : ℝ} (ha : 0 < a) :
    RiemannHypothesis ↔ ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) →
        primeReflectedDifferenceEnergy (shiftedGroundState a) u ≤
          (2 * archSameSideEnergy (shiftedGroundState a) u -
            archReflectedDifferenceEnergy (shiftedGroundState a) u) +
          2 * primeSameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  rw [riemannHypothesis_iff_forall_poleFreeVariationInequality ha]
  refine forall_congr' fun u => forall_congr' fun _ => forall_congr' fun _ =>
    forall_congr' fun _ => ?_
  rw [sameSideEnergy_eq_arch_add_prime, reflectedDifferenceEnergy_eq_arch_add_prime]
  constructor <;> intro h <;> linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
