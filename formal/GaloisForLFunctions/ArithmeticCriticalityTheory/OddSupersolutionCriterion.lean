import GaloisForLFunctions.ArithmeticCriticalityTheory.DoobJumpFoldedGroundStateRepresentation

/-!
# The folded ground-state representation of the Markov energy and the supersolution criterion

Integrating the single-shift folded ground-state representation against the jump measure
`ω(t) dt + Σ_n Λ(n) n^{−1/2} δ_{log n}` gives, for an odd Doob test `v = ω u`,

    markovEnergy (Φ v) = groundRemainder ω u
      + 2 ∫_{x>0} u(x)² ω(x) [ (𝓛_N ω)(x) − Φ(x) cosh(x/2) ω(x) ] dx,

with a nonnegative remainder whenever `ω ≥ 0` on `(0,∞)`. The exchange of the shift integration with
the half-line integration is the only analytic input; it is recorded as the explicit integrability
data `FoldedAdmissible ω u`.

Consequence: if the folded generator dominates the potential, `𝓛_N ω ≥ Φ cosh(x/2) ω` on `(0,∞)`,
then the Markov energy of every odd test factoring admissibly through `ω` is nonnegative, and if every
odd test factors in this way, the Riemann Hypothesis follows through the corpus's odd pure-Dirichlet
Poincaré criterion.
-/

open MeasureTheory Set Filter Topology
open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The nonnegative remainder of one shift: twice the same-side half-line ground jump plus the
reflected collar ground jump. -/
def groundRemainderShift (ω u : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x) +
    ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x

/-- The potential density `u(x)² ω(x) · foldedShiftGenerator ω t x` of one shift. -/
def groundPotentialDensity (ω u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  u x ^ 2 * ω x * foldedShiftGenerator ω t x

/-- The folded generator `𝓛_N ω`: archimedean shifts against the Lévy density plus prime shifts
against the von Mangoldt atoms. -/
def foldedGenerator (ω : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
    ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x

/-- The total nonnegative remainder of the folded ground-state representation. -/
def groundRemainder (ω u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * groundRemainderShift ω u t) +
    ∑' n : ℕ, vonMangoldtAtom n * groundRemainderShift ω u (Real.log n)

/-- Integrability data permitting the exchange of the shift integration with the half-line
integration in the folded ground-state representation. -/
structure FoldedAdmissible (ω u : ℝ → ℝ) : Prop where
  arch_remainder :
    IntegrableOn (fun t => archLevyDensity t * groundRemainderShift ω u t) (Ioi 0)
  arch_potential :
    Integrable (Function.uncurry fun t x => archLevyDensity t * groundPotentialDensity ω u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))
  prime_remainder :
    Summable fun n : ℕ => vonMangoldtAtom n * groundRemainderShift ω u (Real.log n)
  prime_potential :
    Summable fun n : ℕ =>
      ∫ x in Ioi (0 : ℝ), ‖vonMangoldtAtom n * groundPotentialDensity ω u (Real.log n) x‖
  prime_generator :
    IntegrableOn
      (fun x => u x ^ 2 * ω x * ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x)
      (Ioi 0)

theorem continuous_foldedShiftGenerator {ω : ℝ → ℝ} (hω : Continuous ω) (t : ℝ) :
    Continuous (foldedShiftGenerator ω t) := by
  unfold foldedShiftGenerator
  have hΦ := continuous_riemannKernelReal
  exact hΦ.mul (((hΦ.comp (continuous_id.add continuous_const)).mul
    (hω.sub (hω.comp (continuous_id.add continuous_const)))).add
    ((hΦ.comp (continuous_id.sub continuous_const)).mul
      (hω.sub (hω.comp (continuous_abs.comp (continuous_id.sub continuous_const))))))

theorem integrableOn_groundPotentialDensity {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) (huc : HasCompactSupport u) (t : ℝ) (s : Set ℝ) :
    IntegrableOn (fun x => groundPotentialDensity ω u t x) s := by
  have hcont : Continuous fun x => groundPotentialDensity ω u t x := by
    unfold groundPotentialDensity
    exact ((hu.pow 2).mul hω).mul (continuous_foldedShiftGenerator hω t)
  have hsupp : HasCompactSupport fun x => groundPotentialDensity ω u t x := by
    unfold groundPotentialDensity
    exact ((hasCompactSupport_sq huc).mul_right).mul_right
  exact (hcont.integrable_of_hasCompactSupport hsupp).integrableOn

theorem groundRemainderShift_nonneg {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ groundRemainderShift ω u t := by
  unfold groundRemainderShift
  have h1 : 0 ≤ ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx => sameSideGroundJump_nonneg hpos ht hx
  have h2 : 0 ≤ ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x :=
    setIntegral_nonneg measurableSet_Ioo fun x hx => reflectedGroundJump_nonneg hpos hx.1 hx.2
  linarith

theorem groundRemainder_nonneg {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x) :
    0 ≤ groundRemainder ω u := by
  unfold groundRemainder
  have h1 : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * groundRemainderShift ω u t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le
        (groundRemainderShift_nonneg hpos (mem_Ioi.mp ht).le)
  have h2 : 0 ≤ ∑' n : ℕ, vonMangoldtAtom n * groundRemainderShift ω u (Real.log n) :=
    tsum_nonneg fun n =>
      mul_nonneg (vonMangoldtAtom_nonneg n)
        (groundRemainderShift_nonneg hpos (Real.log_natCast_nonneg n))
  linarith

theorem phiDoobPrimeJump_eq_atom_mul_shiftJump (v : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    phiDoobPrimeJump v n x = vonMangoldtAtom n * phiDoobArchShiftJump v (Real.log n) x := by
  unfold phiDoobPrimeJump phiDoobArchShiftJump
  ring

/-- **Folded ground-state representation of the Markov energy.** -/
theorem markovEnergy_phiDoob_eq_groundRemainder_add_potential {ω u : ℝ → ℝ}
    (hω : ContDiff ℝ 2 ω) (hodd : ∀ x, ω (-x) = -ω x)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hadm : FoldedAdmissible ω u) :
    markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) =
      groundRemainder ω u +
        2 * ∫ x in Ioi (0 : ℝ),
          u x ^ 2 * ω x * (foldedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x) := by
  set v : ℝ → ℝ := fun y => ω y * u y with hv_def
  have hωc : Continuous ω := hω.continuous
  have huco : Continuous u := hu.continuous
  have hv2 : ContDiff ℝ 2 v := hω.mul hu
  have hvc : HasCompactSupport v := huc.mul_left
  have hvcont : Continuous v := hωc.mul huco
  have hvodd : ∀ x, v (-x) = -v x := by
    intro x
    simp only [hv_def, hodd x, heven x]
    ring
  -- one shift
  have hJ : ∀ t : ℝ, 0 ≤ t → (∫ x : ℝ, phiDoobArchShiftJump v t x) =
      groundRemainderShift ω u t + 2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u t x := by
    intro t ht
    rw [integral_phiDoobArchShiftJump_groundState hωc hodd huco huc heven ht]
    unfold groundRemainderShift groundPotentialDensity
    ring
  rw [phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv2 hvc]
  -- the archimedean part
  have hF : ∀ t x : ℝ, archLevyDensity t * groundPotentialDensity ω u t x =
      u x ^ 2 * ω x * (archLevyDensity t * foldedShiftGenerator ω t x) := by
    intro t x
    unfold groundPotentialDensity
    ring
  have hpot_int : IntegrableOn
      (fun t => archLevyDensity t * (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u t x))
      (Ioi 0) := by
    have h := (hadm.arch_potential.integral_prod_left).const_mul 2
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [integral_const_mul]
    ring
  have harch : phiDoobArchJumpEnergy v =
      (∫ t in Ioi (0 : ℝ), archLevyDensity t * groundRemainderShift ω u t) +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x *
          ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x := by
    unfold phiDoobArchJumpEnergy
    have h1 : (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x : ℝ, phiDoobArchShiftJump v t x) =
        ∫ t in Ioi (0 : ℝ), (archLevyDensity t * groundRemainderShift ω u t +
          archLevyDensity t * (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u t x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [hJ t (mem_Ioi.mp ht).le]
      ring
    rw [h1, integral_add hadm.arch_remainder hpot_int]
    congr 1
    have h2 : (∫ t in Ioi (0 : ℝ),
        archLevyDensity t * (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u t x)) =
        2 * ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ),
          archLevyDensity t * groundPotentialDensity ω u t x := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      rw [integral_const_mul]
      ring
    rw [h2, integral_integral_swap hadm.arch_potential]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact hF t x
  -- the prime part
  have hprime_term : ∀ n : ℕ, (∫ x : ℝ, phiDoobPrimeJump v n x) =
      vonMangoldtAtom n * groundRemainderShift ω u (Real.log n) +
        vonMangoldtAtom n * (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u (Real.log n) x) := by
    intro n
    have h := hJ (Real.log n) (Real.log_natCast_nonneg n)
    simp_rw [phiDoobPrimeJump_eq_atom_mul_shiftJump v n]
    rw [integral_const_mul, h]
    ring
  have hsum2 : Summable fun n : ℕ =>
      vonMangoldtAtom n * (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u (Real.log n) x) := by
    refine Summable.of_norm_bounded (hadm.prime_potential.mul_left 2) fun n => ?_
    have h1 : vonMangoldtAtom n * (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u (Real.log n) x)
        = 2 * ∫ x in Ioi (0 : ℝ), vonMangoldtAtom n * groundPotentialDensity ω u (Real.log n) x := by
      rw [integral_const_mul]
      ring
    rw [h1, norm_mul, Real.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)
  have hprime : (∑' n : ℕ, ∫ x : ℝ, phiDoobPrimeJump v n x) =
      (∑' n : ℕ, vonMangoldtAtom n * groundRemainderShift ω u (Real.log n)) +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x *
          ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x := by
    rw [tsum_congr hprime_term, hadm.prime_remainder.tsum_add hsum2]
    congr 1
    have h1 : (∑' n : ℕ, vonMangoldtAtom n *
        (2 * ∫ x in Ioi (0 : ℝ), groundPotentialDensity ω u (Real.log n) x)) =
        2 * ∑' n : ℕ, ∫ x in Ioi (0 : ℝ),
          vonMangoldtAtom n * groundPotentialDensity ω u (Real.log n) x := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n => ?_
      rw [integral_const_mul]
      ring
    rw [h1, integral_tsum_of_summable_integral_norm
      (F := fun n : ℕ => fun x => vonMangoldtAtom n * groundPotentialDensity ω u (Real.log n) x)
      (fun n : ℕ => (integrableOn_groundPotentialDensity hωc huco huc (Real.log n) _).const_mul _)
      hadm.prime_potential]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    unfold groundPotentialDensity
    ring
  -- the potential
  have hcosh : phiDoobCoshMass (fun x => v x ^ 2) =
      2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x * (riemannKernelReal x * Real.cosh (x / 2) * ω x) := by
    rw [phiDoobCoshMass_sq_eq_two_mul_integral_Ioi_of_odd hvcont hvc hvodd]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [hv_def]
    ring
  -- integrability of the three half-line pieces
  have hint_arch : IntegrableOn (fun x => u x ^ 2 * ω x *
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) (Ioi 0) := by
    have h := hadm.arch_potential.integral_prod_right
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact hF t x
  have hint_cosh : IntegrableOn (fun x => u x ^ 2 * ω x *
      (riemannKernelReal x * Real.cosh (x / 2) * ω x)) (Ioi 0) := by
    have hcont : Continuous fun x => u x ^ 2 * ω x *
        (riemannKernelReal x * Real.cosh (x / 2) * ω x) :=
      ((huco.pow 2).mul hωc).mul ((continuous_riemannKernelReal.mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul hωc)
    have hsupp : HasCompactSupport fun x => u x ^ 2 * ω x *
        (riemannKernelReal x * Real.cosh (x / 2) * ω x) :=
      ((hasCompactSupport_sq huc).mul_right).mul_right
    exact (hcont.integrable_of_hasCompactSupport hsupp).integrableOn
  rw [harch, hprime, hcosh]
  unfold groundRemainder foldedGenerator
  have hint_ap : IntegrableOn (fun x =>
      u x ^ 2 * ω x * (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
        u x ^ 2 * ω x * ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x)
      (Ioi 0) := hint_arch.add hadm.prime_generator
  have hsplit : (∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x *
      ((∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
        (∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x) -
        riemannKernelReal x * Real.cosh (x / 2) * ω x)) =
      (∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x *
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
      (∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x *
        ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x) -
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x * (riemannKernelReal x * Real.cosh (x / 2) * ω x) := by
    have h1 : (∫ x in Ioi (0 : ℝ), u x ^ 2 * ω x *
        ((∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
          (∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x) -
          riemannKernelReal x * Real.cosh (x / 2) * ω x)) =
        ∫ x in Ioi (0 : ℝ),
          ((u x ^ 2 * ω x * (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
            u x ^ 2 * ω x * ∑' n : ℕ, vonMangoldtAtom n * foldedShiftGenerator ω (Real.log n) x) -
            u x ^ 2 * ω x * (riemannKernelReal x * Real.cosh (x / 2) * ω x)) :=
      setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
    rw [h1, integral_sub hint_ap hint_cosh, integral_add hint_arch hadm.prime_generator]
  rw [hsplit]
  ring

/-- **Sufficiency of a folded supersolution.** If `ω` is odd, nonnegative on `(0,∞)` and
`Φ(x) cosh(x/2) ω(x) ≤ (𝓛_N ω)(x)` for `x > 0`, the Markov energy of every admissible odd Doob test
`Φ(ω u)` is nonnegative. -/
theorem markovEnergy_phiDoob_nonneg_of_foldedSupersolution {ω u : ℝ → ℝ}
    (hω : ContDiff ℝ 2 ω) (hodd : ∀ x, ω (-x) = -ω x) (hpos : ∀ x, 0 < x → 0 ≤ ω x)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hadm : FoldedAdmissible ω u)
    (hsuper : ∀ x, 0 < x →
      riemannKernelReal x * Real.cosh (x / 2) * ω x ≤ foldedGenerator ω x) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) := by
  rw [markovEnergy_phiDoob_eq_groundRemainder_add_potential hω hodd hu huc heven hadm]
  have h1 := groundRemainder_nonneg (u := u) hpos
  have h2 : 0 ≤ ∫ x in Ioi (0 : ℝ),
      u x ^ 2 * ω x * (foldedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x) := by
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hx0 := mem_Ioi.mp hx
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hpos x hx0)) (sub_nonneg.mpr (hsuper x hx0))
  linarith

/-- **Folded supersolution criterion for the Riemann Hypothesis.** If an odd `C²` function `ω`,
nonnegative on `(0,∞)`, is a supersolution of the folded generator against the potential
`Φ(x) cosh(x/2)`, and every odd `C²_c` test factors admissibly through `ω`, then the Riemann
Hypothesis holds. -/
theorem riemannHypothesis_of_foldedSupersolution {ω : ℝ → ℝ}
    (hω : ContDiff ℝ 2 ω) (hodd : ∀ x, ω (-x) = -ω x) (hpos : ∀ x, 0 < x → 0 ≤ ω x)
    (hsuper : ∀ x, 0 < x →
      riemannKernelReal x * Real.cosh (x / 2) * ω x ≤ foldedGenerator ω x)
    (hfactor : ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
      ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧ (∀ x, u (-x) = u x) ∧
        (∀ x, v x = ω x * u x) ∧ FoldedAdmissible ω u) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare]
  intro v hv hvc hvodd
  obtain ⟨u, hu, huc, heven, hvu, hadm⟩ := hfactor v hv hvc hvodd
  have hveq : v = fun y => ω y * u y := funext hvu
  have hM := markovEnergy_phiDoob_nonneg_of_foldedSupersolution hω hodd hpos hu huc heven hadm hsuper
  rw [← hveq] at hM
  rw [phiDoob_markovEnergy_eq_archJump_add_primeJump_sub_coshMass hv hvc] at hM
  linarith

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
