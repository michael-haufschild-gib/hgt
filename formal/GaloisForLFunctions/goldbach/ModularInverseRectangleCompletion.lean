import GaloisForLFunctions.goldbach.KloostermanConductorReduction
import GaloisForLFunctions.RHTower.Sieve.KloostermanCrossPhaseGeometric
import GaloisForLFunctions.RHTower.Sieve.KuzminLandau
import GaloisForLFunctions.RHTower.SquareResidueQuadraticInterval
import GaloisForLFunctions.RHTower.Sieve.KloostermanRamanujanDivisorSum
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
# Modular-inverse rectangles

Finite interval transforms descend exactly on divisor frequency progressions.
The Ramanujan axes retain their sharp gcd bounds, while the remaining frequencies
use the composite cubic Kloosterman estimate and a summable divisor weight.
-/

namespace GaloisForLFunctions.Goldbach

open Finset RHTower.Sieve
open scoped BigOperators

noncomputable section
set_option autoImplicit false

/-! ## The actual finite interval transform -/

/-- Fourier coefficient of the integer interval starting at `A` with length `L`. -/
def intervalAdditiveFourier (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) : ℂ :=
  ∑ j ∈ range L, ZMod.stdAddChar (-a * ((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))))

/-- Distance of a frequency to either endpoint of its canonical residue interval. -/
def residueEdge (M : ℕ+) (a : ZMod (M : ℕ)) : ℕ :=
  min a.val ((M : ℕ) - a.val)

theorem residueEdge_pos_iff (M : ℕ+) (a : ZMod (M : ℕ)) :
    0 < residueEdge M a ↔ a ≠ 0 := by
  constructor
  · intro h ha
    subst a
    simp [residueEdge] at h
  · intro ha
    have ha0 : 0 < a.val := Nat.pos_of_ne_zero
      (fun h => ha ((ZMod.val_eq_zero a).mp h))
    exact lt_min ha0 (Nat.sub_pos_of_lt (ZMod.val_lt a))

theorem intervalAdditiveFourier_zero (M : ℕ+) (A : ℤ) (L : ℕ) :
    intervalAdditiveFourier M A L 0 = L := by
  simp [intervalAdditiveFourier]

/-- The starting point contributes one unit phase; every endpoint stays in the geometric sum. -/
theorem intervalAdditiveFourier_eq_phase_mul_geometric
    (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) :
    intervalAdditiveFourier M A L a =
      ZMod.stdAddChar (-a * (A : ZMod (M : ℕ))) *
        ∑ j ∈ range L, (ZMod.stdAddChar (-a)) ^ j := by
  rw [intervalAdditiveFourier, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [show -a * ((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))) =
      -a * (A : ZMod (M : ℕ)) + j • (-a) by simp only [nsmul_eq_mul]; ring,
    AddChar.map_add_eq_mul, stdAddChar_nsmul_eq_pow]

/-- Exact sine chord of a finite additive frequency, including frequency zero. -/
theorem norm_stdAddChar_chord_eq (M : ℕ+) (a : ZMod (M : ℕ)) :
    ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (M : ℝ)) := by
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have hval : (a.val : ℝ) ≤ (M : ℝ) := by exact_mod_cast (ZMod.val_lt a).le
  have hβ0 : 0 ≤ (a.val : ℝ) / (M : ℝ) := by positivity
  have hβ1 : (a.val : ℝ) / (M : ℝ) ≤ 1 :=
    (div_le_iff₀ hM).mpr (by simpa only [one_mul] using hval)
  have hsin : 0 ≤ Real.sin (Real.pi * (a.val : ℝ) / (M : ℝ)) := by
    rw [mul_div_assoc]
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · exact mul_nonneg Real.pi_pos.le hβ0
    · nlinarith [Real.pi_pos]
  have hchar : ZMod.stdAddChar a =
      Complex.exp (((2 * Real.pi * (a.val : ℝ) / (M : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast
    ring
  rw [hchar, RHTower.one_sub_exp_mul_I_eq, norm_mul,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [show (2 * Real.pi * (a.val : ℝ) / (M : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (M : ℝ) by ring]
  exact abs_of_nonneg (mul_nonneg (by norm_num) hsin)

/-- The character chord pays for distance from the zero frequency. -/
theorem residueEdge_le_stdAddChar_chord (M : ℕ+) (a : ZMod (M : ℕ)) :
    4 * (residueEdge M a : ℝ) / (M : ℝ) ≤ ‖1 - ZMod.stdAddChar a‖ := by
  by_cases ha : a = 0
  · subst a
    simp [residueEdge]
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have he : (0 : ℝ) < (residueEdge M a : ℝ) := by
    exact_mod_cast (residueEdge_pos_iff M a).mpr ha
  have hleft : (residueEdge M a : ℝ) ≤ (a.val : ℝ) := by
    exact_mod_cast min_le_left a.val ((M : ℕ) - a.val)
  have hright : (residueEdge M a : ℝ) + (a.val : ℝ) ≤ (M : ℝ) := by
    have h := Nat.cast_le (α := ℝ) |>.mpr (min_le_right a.val ((M : ℕ) - a.val))
    rw [Nat.cast_sub (ZMod.val_lt a).le] at h
    change (residueEdge M a : ℝ) ≤ (M : ℝ) - (a.val : ℝ) at h
    linarith
  have hβ : (a.val : ℝ) / (M : ℝ) ≤ 1 - (residueEdge M a : ℝ) / (M : ℝ) := by
    have h := (div_le_iff₀ hM).mpr
      (show (residueEdge M a : ℝ) + (a.val : ℝ) ≤ 1 * (M : ℝ) by simpa using hright)
    rw [add_div] at h
    linarith
  have hsin := _root_.RHTower.Sieve.two_mul_le_sin_pi_mul
    (div_pos he hM) (div_le_div_of_nonneg_right hleft hM.le) hβ
  rw [norm_stdAddChar_chord_eq]
  simp only [mul_div_assoc] at hsin ⊢
  linarith

/-- Opposite frequencies have the same character chord. -/
theorem norm_stdAddChar_neg_chord_eq (M : ℕ+) (a : ZMod (M : ℕ)) :
    ‖1 - ZMod.stdAddChar (-a)‖ = ‖1 - ZMod.stdAddChar a‖ := by
  rw [AddChar.map_neg_eq_conj]
  have he : (1 : ℂ) - (starRingEnd ℂ) (ZMod.stdAddChar a) =
      (starRingEnd ℂ) (1 - ZMod.stdAddChar a) := by rw [map_sub, map_one]
  rw [he, Complex.norm_conj]

/-- A finite interval has geometric cancellation at every nonzero frequency. -/
theorem norm_intervalAdditiveFourier_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) :
    ‖intervalAdditiveFourier M A L a‖ ≤
      if a = 0 then (L : ℝ) else (M : ℝ) / (2 * (residueEdge M a : ℝ)) := by
  classical
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl, intervalAdditiveFourier_zero, Complex.norm_natCast]
  rw [if_neg ha]
  have hne : ZMod.stdAddChar (-a) ≠ (1 : ℂ) := by
    intro h
    exact ha (neg_eq_zero.mp ((stdAddChar_eq_one_iff (M : ℕ) (-a)).mp h))
  have hgeom := _root_.RHTower.norm_geom_sum_le
    (show ‖ZMod.stdAddChar (-a)‖ = 1 by simp) hne L
  rw [intervalAdditiveFourier_eq_phase_mul_geometric, norm_mul]
  rw [show ‖ZMod.stdAddChar (-a * (A : ZMod (M : ℕ)))‖ = 1 by simp, one_mul]
  rw [norm_stdAddChar_neg_chord_eq] at hgeom
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have he : (0 : ℝ) < (residueEdge M a : ℝ) := by
    exact_mod_cast (residueEdge_pos_iff M a).mpr ha
  refine hgeom.trans ?_
  calc
    _ ≤ 2 / (4 * (residueEdge M a : ℝ) / (M : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (residueEdge_le_stdAddChar_chord M a)
    _ = (M : ℝ) / (2 * (residueEdge M a : ℝ)) := by field_simp; ring

/-- Translation preserves the norm of the actual finite prefix. -/
theorem norm_intervalAdditiveFourier_eq_prefix
    (M : ℕ+) (A : ℤ) (L : ℕ) (a : ZMod (M : ℕ)) :
    ‖intervalAdditiveFourier M A L a‖ =
      ‖_root_.RHTower.squareResidueLinearPrefix a L‖ := by
  have hfactor : intervalAdditiveFourier M A L a =
      ZMod.stdAddChar (-a * (A : ZMod (M : ℕ))) *
        _root_.RHTower.squareResidueLinearPrefix a L := by
    rw [intervalAdditiveFourier, _root_.RHTower.squareResidueLinearPrefix, mul_sum]
    apply sum_congr rfl
    intro j _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hfactor, norm_mul,
    show ‖ZMod.stdAddChar (-a * (A : ZMod (M : ℕ)))‖ = 1 by simp, one_mul]

/-- Total Fourier mass after deleting the zero frequency. -/
def intervalNonzeroFourierMass (M : ℕ+) (A : ℤ) (L : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ‖intervalAdditiveFourier M A L a‖

/-- The logarithmic budget is uniform in both interval length and starting point. -/
theorem intervalNonzeroFourierMass_le (M : ℕ+) (A : ℤ) (L : ℕ) :
    intervalNonzeroFourierMass M A L ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  classical
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        2 / ‖1 - ZMod.stdAddChar a‖ := by
      apply sum_le_sum
      intro a ha
      have ha0 := (mem_filter.mp ha).2
      rw [norm_intervalAdditiveFourier_eq_prefix]
      have h := _root_.RHTower.norm_squareResidueLinearPrefix_le_cap a L
      rw [if_neg ha0] at h
      rw [norm_stdAddChar_neg_chord_eq] at h
      exact h.trans (min_le_right _ _)
    _ ≤ ∑ a : ZMod (M : ℕ), 2 / ‖1 - ZMod.stdAddChar a‖ :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
    _ ≤ _ := _root_.RHTower.squareResidue_sum_reciprocalChord_le

/-- Positive quotient attached to an actual divisor of the modulus. -/
def modulusDivisorQuotient (M : ℕ+) (d : {d : ℕ // d ∈ (M : ℕ).divisors}) : ℕ+ :=
  ⟨(M : ℕ) / d.val,
    Nat.div_pos (Nat.le_of_dvd M.pos (Nat.dvd_of_mem_divisors d.property))
      (Nat.pos_of_mem_divisors d.property)⟩

/-- Canonical representatives agree with the inverse of the finite cyclic equivalence. -/
theorem finEquiv_symm_val (M : ℕ+) (a : ZMod (M : ℕ)) :
    ((ZMod.finEquiv (M : ℕ)).symm a).val = a.val := by
  rcases M with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ n => rfl

/-- All frequencies divisible by `d` are exactly the frequencies at modulus `M/d`. -/
def divisorFrequencyEquiv (M : ℕ+) (d : {d : ℕ // d ∈ (M : ℕ).divisors}) :
    ZMod (modulusDivisorQuotient M d : ℕ) ≃
      {a : ZMod (M : ℕ) // d.val ∣ a.val} :=
  (ZMod.finEquiv (modulusDivisorQuotient M d : ℕ)).toEquiv.symm.trans
    (ramanujanMultiplesFinEquiv M.pos d.property)

theorem divisorFrequencyEquiv_apply (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors})
    (a : ZMod (modulusDivisorQuotient M d : ℕ)) :
    (divisorFrequencyEquiv M d a).val = ((d.val * a.val : ℕ) : ZMod (M : ℕ)) := by
  change ((d.val * ((ZMod.finEquiv (modulusDivisorQuotient M d : ℕ)).symm a).val : ℕ) :
    ZMod (M : ℕ)) = _
  rw [finEquiv_symm_val]

/-- A restricted interval character descends exactly, including negative starting points. -/
theorem intervalAdditiveFourier_divisorFrequency (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ)
    (a : ZMod (modulusDivisorQuotient M d : ℕ)) :
    intervalAdditiveFourier M A L (divisorFrequencyEquiv M d a).val =
      intervalAdditiveFourier (modulusDivisorQuotient M d) A L a := by
  let q := modulusDivisorQuotient M d
  letI : NeZero ((M : ℕ) / d.val) := ⟨q.pos.ne'⟩
  have hqd : (q : ℕ) ∣ (M : ℕ) :=
    ⟨d.val, (Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)).symm⟩
  have hreduce (z : ZMod (M : ℕ)) :
      (z.val : ZMod (q : ℕ)) = ZMod.castHom hqd (ZMod (q : ℕ)) z := by
    conv_rhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [divisorFrequencyEquiv_apply, intervalAdditiveFourier, intervalAdditiveFourier]
  apply sum_congr rfl
  intro j _
  have h := stdAddChar_divisorMultiple M.pos d.property
    (-((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))))
    (⟨a.val, ZMod.val_lt a⟩ : Fin (q : ℕ))
  change ZMod.stdAddChar (((d.val * a.val : ℕ) : ZMod (M : ℕ)) *
      -((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)))) =
    ZMod.stdAddChar ((a.val : ZMod (q : ℕ)) *
      ((-((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)))).val : ZMod (q : ℕ))) at h
  rw [hreduce, map_neg, map_add, map_intCast, map_natCast,
    ZMod.natCast_zmod_val] at h
  simpa only [neg_mul, mul_neg] using h

/-- Nonzero interval Fourier mass on the literal divisibility progression. -/
def intervalDivisorFourierMass (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0 ∧ d.val ∣ a.val),
    ‖intervalAdditiveFourier M A L a‖

/-- Restricting frequencies divides the modulus without any loss in the finite transform. -/
theorem intervalDivisorFourierMass_eq (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) :
    intervalDivisorFourierMass M d A L =
      intervalNonzeroFourierMass (modulusDivisorQuotient M d) A L := by
  classical
  let e := divisorFrequencyEquiv M d
  have he0 : (e 0).val = 0 := by simp [e, divisorFrequencyEquiv_apply]
  have hzero (a : ZMod (modulusDivisorQuotient M d : ℕ)) :
      (e a).val = 0 ↔ a = 0 := by
    constructor
    · intro ha
      apply e.injective
      exact Subtype.ext (ha.trans he0.symm)
    · rintro rfl
      exact he0
  calc
    _ = ∑ x : {a : ZMod (M : ℕ) // d.val ∣ a.val},
        if x.val = 0 then 0 else ‖intervalAdditiveFourier M A L x.val‖ := by
      rw [intervalDivisorFourierMass,
        ← sum_subtype (univ.filter (fun a : ZMod (M : ℕ) => d.val ∣ a.val))
          (by simp) (fun a => if a = 0 then 0 else ‖intervalAdditiveFourier M A L a‖)]
      simp only [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> by_cases hd : d.val ∣ a.val <;> simp [ha, hd]
    _ = ∑ a : ZMod (modulusDivisorQuotient M d : ℕ),
        if (e a).val = 0 then 0 else ‖intervalAdditiveFourier M A L (e a).val‖ :=
      (e.sum_comp (fun x => if x.val = 0 then 0 else
        ‖intervalAdditiveFourier M A L x.val‖)).symm
    _ = _ := by
      rw [intervalNonzeroFourierMass, sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp [ha, he0]
      · have hz : (e a).val ≠ 0 := fun h => ha ((hzero a).mp h)
        simp only [if_neg hz, if_pos ha]
        rw [show e a = divisorFrequencyEquiv M d a by rfl,
          intervalAdditiveFourier_divisorFrequency]

/-- The progression-sensitive logarithmic budget pays `M/d`, not `M`. -/
theorem intervalDivisorFourierMass_le (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) :
    intervalDivisorFourierMass M d A L ≤
      (modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ)) := by
  rw [intervalDivisorFourierMass_eq]
  refine (intervalNonzeroFourierMass_le _ A L).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hlog : Real.log (modulusDivisorQuotient M d : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (modulusDivisorQuotient M d).pos)
    exact_mod_cast Nat.div_le_self (M : ℕ) d.val
  linarith

/-! ## The two frequency axes -/

/-- The zero second frequency is the actual Ramanujan sum. -/
theorem kloostermanSum_axis_eq_ramanujan (M : ℕ+) (a : ZMod (M : ℕ)) :
    kloostermanSum (M : ℕ) a 0 =
      _root_.RHTower.cglRamanujanAdditiveSum ⟨(M : ℕ), M.pos⟩ a := by
  classical
  unfold kloostermanSum kloostermanPhase _root_.RHTower.cglRamanujanAdditiveSum
  simp only [zero_mul, add_zero]
  refine sum_bij' (fun u _ => (u : ZMod (M : ℕ)))
    (fun b hb => (mem_filter.mp hb).2.unit)
    (fun u _ => mem_filter.mpr ⟨mem_univ _, u.isUnit⟩)
    (fun _ _ => mem_univ _)
    (fun u _ => by ext; simp) (fun b hb => by simp) ?_
  intro u _
  rw [mul_comm]

/-- A unit frequency has the primitive Ramanujan value, at every positive modulus. -/
theorem kloostermanSum_unit_zero_eq_moebius (M : ℕ+) (u : (ZMod (M : ℕ))ˣ) :
    kloostermanSum (M : ℕ) (u : ZMod (M : ℕ)) 0 =
      ((ArithmeticFunction.moebius (M : ℕ) : ℤ) : ℂ) := by
  have hcop : Nat.Coprime (u : ZMod (M : ℕ)).val (M : ℕ) :=
    (ZMod.isUnit_iff_coprime _ _).mp (by
      simpa only [ZMod.natCast_zmod_val] using u.isUnit)
  rw [kloostermanSum_axis_eq_ramanujan,
    cglRamanujanAdditiveSum_eq_gcd_mobiusDivisorSum_sieve]
  change (∑ d ∈ (Nat.gcd (u : ZMod (M : ℕ)).val (M : ℕ)).divisors,
    (d : ℂ) * ((ArithmeticFunction.moebius ((M : ℕ) / d) : ℤ) : ℂ)) = _
  rw [hcop.gcd_eq_one]
  simp

theorem norm_kloostermanSum_unit_zero_le (M : ℕ+) (u : (ZMod (M : ℕ))ˣ) :
    ‖kloostermanSum (M : ℕ) (u : ZMod (M : ℕ)) 0‖ ≤ 1 := by
  rw [kloostermanSum_unit_zero_eq_moebius, Complex.norm_intCast]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := (M : ℕ))

/-- Conductor fibres give the sharp gcd bound on each Ramanujan axis. -/
theorem norm_kloostermanSum_axis_le_gcd (M : ℕ+) (a : ZMod (M : ℕ)) :
    ‖kloostermanSum (M : ℕ) a 0‖ ≤ (Nat.gcd (M : ℕ) a.val : ℝ) := by
  let g : ℕ+ := ⟨Nat.gcd (M : ℕ) a.val, Nat.gcd_pos_of_pos_left a.val M.pos⟩
  have hgM : (g : ℕ) ∣ (M : ℕ) := Nat.gcd_dvd_left _ _
  have hga : (g : ℕ) ∣ a.val := Nat.gcd_dvd_right _ _
  let q : ℕ+ := ⟨(M : ℕ) / (g : ℕ),
    Nat.div_pos (Nat.le_of_dvd M.pos hgM) g.pos⟩
  have hM : (M : ℕ) = (q : ℕ) * (g : ℕ) := (Nat.div_mul_cancel hgM).symm
  have ha : (g : ℕ) * (a.val / (g : ℕ)) = a.val := Nat.mul_div_cancel' hga
  have hc : Nat.Coprime (a.val / (g : ℕ)) (q : ℕ) := by
    apply Nat.coprime_iff_gcd_eq_one.mpr
    apply Nat.mul_left_cancel g.pos
    rw [← Nat.gcd_mul_left, ha]
    have hq : (g : ℕ) * (q : ℕ) = (M : ℕ) := by simpa [Nat.mul_comm] using hM.symm
    rw [hq, Nat.mul_one]
    exact Nat.gcd_comm _ _
  have hu : IsUnit ((a.val / (g : ℕ) : ℕ) : ZMod (q : ℕ)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr hc
  have hs : ‖kloostermanSum (q : ℕ)
      ((a.val / (g : ℕ) : ℕ) : ZMod (q : ℕ)) 0‖ ≤ 1 := by
    simpa only [hu.unit_spec] using norm_kloostermanSum_unit_zero_le q hu.unit
  have htransport (N : ℕ) (hN : N = (q : ℕ) * (g : ℕ)) :
      letI : NeZero N := ⟨by rw [hN]; exact Nat.mul_ne_zero q.pos.ne' g.pos.ne'⟩
      ‖kloostermanSum N (a.val : ZMod N) 0‖ ≤ (g : ℝ) := by
    subst N
    have h := norm_kloostermanSum_factor_lift_le q g ((a.val / (g : ℕ) : ℕ) : ℤ) 0
    simp only [Int.cast_natCast, Int.cast_zero, mul_zero] at h
    have hcoef : ((g : ℕ) : ZMod ((q : ℕ) * (g : ℕ))) *
        ((a.val / (g : ℕ) : ℕ) : ZMod ((q : ℕ) * (g : ℕ))) =
          (a.val : ZMod ((q : ℕ) * (g : ℕ))) := by
      rw [← Nat.cast_mul, ha]
    rw [hcoef] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _))
  have hgcast : (g : ℝ) = (Nat.gcd (M : ℕ) a.val : ℝ) := rfl
  have ht := htransport (M : ℕ) hM
  rw [hgcast] at ht
  simpa only [ZMod.natCast_zmod_val] using ht


/-! ## Exact divisibility of the frequency gcd -/

/-- Two gcd extractions retain the product factor without a valuation argument. -/
theorem gcd_product_dvd_gcd_product (M b c : ℕ) :
    Nat.gcd M (b * c) ∣ Nat.gcd M b * Nat.gcd M c := by
  let D := Nat.gcd M (b * c)
  have hDM : D ∣ M := Nat.gcd_dvd_left _ _
  have hDbc : D ∣ b * c := Nat.gcd_dvd_right _ _
  have hDgb : D ∣ Nat.gcd M c * b := by
    rw [← Nat.gcd_mul_right]
    exact Nat.dvd_gcd (dvd_mul_of_dvd_left hDM b)
      (by simpa only [Nat.mul_comm] using hDbc)
  have hDgM : D ∣ Nat.gcd M c * M := dvd_mul_of_dvd_right hDM _
  have h := Nat.dvd_gcd hDgM hDgb
  rw [Nat.gcd_mul_left, Nat.mul_comm] at h
  exact h

/-- The three-frequency gcd divides the product of the target gcd and the pair gcd. -/
theorem frequencyGcd_dvd (M a b c : ℕ) :
    Nat.gcd M (Nat.gcd a ((b * c) % M)) ∣
      Nat.gcd M c * Nat.gcd M (Nat.gcd a b) := by
  let D := Nat.gcd M (Nat.gcd a ((b * c) % M))
  have hDM : D ∣ M := Nat.gcd_dvd_left _ _
  have hDa : D ∣ a := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hDmod : D ∣ (b * c) % M :=
    (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hDbc : D ∣ b * c := by
    rw [← Nat.mod_add_div (b * c) M]
    exact dvd_add hDmod (dvd_mul_of_dvd_left hDM _)
  have hD : D ∣ Nat.gcd (Nat.gcd M a) (b * c) :=
    Nat.dvd_gcd (Nat.dvd_gcd hDM hDa) hDbc
  have hc : Nat.gcd (Nat.gcd M a) c ∣ Nat.gcd M c :=
    Nat.dvd_gcd ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _))
      (Nat.gcd_dvd_right _ _)
  have h := hD.trans (gcd_product_dvd_gcd_product (Nat.gcd M a) b c)
  have h' := h.trans (Nat.mul_dvd_mul (dvd_refl (Nat.gcd (Nat.gcd M a) b)) hc)
  simpa only [Nat.gcd_assoc, Nat.mul_comm] using h'

/-- The gcd loss in a Kloosterman frequency is bounded by the actual target gcd. -/
theorem residueFrequencyGcd_le (M : ℕ+) (a b c : ZMod (M : ℕ)) :
    Nat.gcd (M : ℕ) (Nat.gcd a.val (b * c).val) ≤
      Nat.gcd (M : ℕ) c.val * Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) := by
  apply Nat.le_of_dvd
    (Nat.mul_pos (Nat.gcd_pos_of_pos_left _ M.pos) (Nat.gcd_pos_of_pos_left _ M.pos))
  simpa only [ZMod.val_mul] using frequencyGcd_dvd (M : ℕ) a.val b.val c.val


/-! ## Exact finite completion of the inverse graph -/

/-- Number of entries of the actual integer interval in one residue class. -/
def intervalResidueMultiplicity (M : ℕ+) (A : ℤ) (L : ℕ) (x : ZMod (M : ℕ)) : ℕ :=
  ((range L).filter (fun j : ℕ => (A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)) = x)).card

/-- Finite Fourier inversion retains the exact residue multiplicity. -/
theorem intervalResidueMultiplicity_fourier
    (M : ℕ+) (A : ℤ) (L : ℕ) (x : ZMod (M : ℕ)) :
    (M : ℂ) * (intervalResidueMultiplicity M A L x : ℂ) =
      ∑ a : ZMod (M : ℕ), intervalAdditiveFourier M A L a * ZMod.stdAddChar (a * x) := by
  classical
  symm
  calc
    _ = ∑ j ∈ range L, ∑ a : ZMod (M : ℕ),
        ZMod.stdAddChar (a * (x - ((A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ))))) := by
      simp only [intervalAdditiveFourier, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro a _
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    _ = ∑ j ∈ range L,
        if (A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)) = x then (M : ℂ) else 0 := by
      apply sum_congr rfl
      intro j _
      rw [_root_.RHTower.Sieve.sum_stdAddChar_mul]
      simp [sub_eq_zero, eq_comm]
    _ = _ := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, intervalResidueMultiplicity, mul_comm]

/-- Integer interval pairs lying on the unit part of the modular-inverse graph. -/
def modularInverseRectangleCount
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) : ℕ :=
  ∑ u : (ZMod (M : ℕ))ˣ,
    intervalResidueMultiplicity M A L (u : ZMod (M : ℕ)) *
      intervalResidueMultiplicity M B H (c * (↑u⁻¹ : ZMod (M : ℕ)))

/-- Exact double Fourier completion, with no discarded endpoint or frequency term. -/
theorem modularInverseRectangleCount_fourier
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    (M : ℂ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℂ) =
      ∑ a : ZMod (M : ℕ), ∑ b : ZMod (M : ℕ),
        intervalAdditiveFourier M A L a * intervalAdditiveFourier M B H b *
          kloostermanSum (M : ℕ) a (b * c) := by
  rw [modularInverseRectangleCount, Nat.cast_sum, mul_sum]
  calc
    _ = ∑ u : (ZMod (M : ℕ))ˣ,
        ((M : ℂ) * (intervalResidueMultiplicity M A L (u : ZMod (M : ℕ)) : ℂ)) *
          ((M : ℂ) * (intervalResidueMultiplicity M B H
            (c * (↑u⁻¹ : ZMod (M : ℕ))) : ℂ)) := by
      apply sum_congr rfl
      intro u _
      push_cast
      ring
    _ = ∑ u : (ZMod (M : ℕ))ˣ,
        (∑ a : ZMod (M : ℕ), intervalAdditiveFourier M A L a *
          ZMod.stdAddChar (a * (u : ZMod (M : ℕ)))) *
        (∑ b : ZMod (M : ℕ), intervalAdditiveFourier M B H b *
          ZMod.stdAddChar (b * (c * (↑u⁻¹ : ZMod (M : ℕ))))) := by
      simp_rw [intervalResidueMultiplicity_fourier]
    _ = _ := by
      simp only [sum_mul]
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro a _
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [kloostermanSum, mul_sum]
      apply sum_congr rfl
      intro u _
      rw [kloostermanPhase,
        show a * (u : ZMod (M : ℕ)) + (b * c) * (↑u⁻¹ : ZMod (M : ℕ)) =
          a * (u : ZMod (M : ℕ)) + b * (c * (↑u⁻¹ : ZMod (M : ℕ))) by ring,
        AddChar.map_add_eq_mul]
      ring


/-! ## Divisor-weighted Fourier budgets -/

theorem intervalDivisorFourierMass_nonneg (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) (A : ℤ) (L : ℕ) :
    0 ≤ intervalDivisorFourierMass M d A L :=
  sum_nonneg (fun _ _ => norm_nonneg _)

/-- The actual gcd is one of the nonnegative common-divisor terms. -/
theorem residueGcd_le_divisor_sum (M : ℕ+) (a : ZMod (M : ℕ)) :
    (Nat.gcd (M : ℕ) a.val : ℝ) ≤
      ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors}, if d.val ∣ a.val then (d.val : ℝ) else 0 := by
  classical
  let g := Nat.gcd (M : ℕ) a.val
  have hg : g ∈ (M : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, M.pos.ne'⟩
  have h := single_le_sum
    (s := univ)
    (f := fun d : {d : ℕ // d ∈ (M : ℕ).divisors} =>
      if d.val ∣ a.val then (d.val : ℝ) else 0)
    (fun _ _ => by split_ifs <;> positivity)
    (mem_univ (⟨g, hg⟩ : {d : ℕ // d ∈ (M : ℕ).divisors}))
  dsimp [g] at h
  rw [if_pos (Nat.gcd_dvd_right (M : ℕ) a.val)] at h
  exact h

/-- Fourier mass with its exact gcd weight. -/
def intervalGcdFourierMass (M : ℕ+) (A : ℤ) (L : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ‖intervalAdditiveFourier M A L a‖ * (Nat.gcd (M : ℕ) a.val : ℝ)

/-- Summing along divisor progressions costs one divisor count, including every nonprimitive frequency. -/
theorem intervalGcdFourierMass_le (M : ℕ+) (A : ℤ) (L : ℕ) :
    intervalGcdFourierMass M A L ≤
      ((M : ℕ).divisors.card : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ)) := by
  classical
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ‖intervalAdditiveFourier M A L a‖ *
          ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
            if d.val ∣ a.val then (d.val : ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (residueGcd_le_divisor_sum M a) (norm_nonneg _)
    _ = ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (d.val : ℝ) * intervalDivisorFourierMass M d A L := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro d _
      rw [intervalDivisorFourierMass, mul_sum]
      simp only [sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> by_cases hd : d.val ∣ a.val <;> simp [ha, hd, mul_comm]
    _ ≤ ∑ _d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (M : ℝ) * (1 + Real.log (M : ℝ)) := by
      apply sum_le_sum
      intro d _
      have hprod : (d.val : ℝ) * (modulusDivisorQuotient M d : ℝ) = (M : ℝ) := by
        exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors d.property)
      calc
        _ ≤ (d.val : ℝ) *
            ((modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ))) :=
          mul_le_mul_of_nonneg_left (intervalDivisorFourierMass_le M d A L)
            (Nat.cast_nonneg _)
        _ = _ := by rw [← mul_assoc, hprod]
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe, mul_assoc]

/-- The summable divisor weight is bounded independently of the modulus. -/
theorem sum_divisors_rpow_neg_five_thirds_le (M : ℕ+) :
    (∑ d ∈ (M : ℕ).divisors, (d : ℝ) ^ (-(5 / 3 : ℝ))) ≤ 3 := by
  have htail :
      (∑ j ∈ range ((M : ℕ) - 1), ((j + 2 : ℕ) : ℝ) ^ (-(5 / 3 : ℝ))) ≤ 3 / 2 := by
    have h := _root_.RHTower.sum_range_add_rpow_neg_le
      (c := (5 / 3 : ℝ)) (by norm_num) (M := 1) (by norm_num) ((M : ℕ) - 1)
    norm_num at h
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  calc
    _ ≤ ∑ d ∈ range ((M : ℕ) + 1), (d : ℝ) ^ (-(5 / 3 : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg
        (fun d hd => mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hd)))
        (fun _ _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ 3 := by
      have hM : (M : ℕ) + 1 = ((M : ℕ) - 1) + 1 + 1 := by have := M.pos; omega
      rw [hM, sum_range_succ', sum_range_succ']
      norm_num only [Nat.cast_zero, Nat.zero_add, Nat.cast_one,
        Real.zero_rpow (by norm_num : -(5 / 3 : ℝ) ≠ 0), Real.one_rpow, add_zero]
      simpa only [Nat.add_assoc] using (show
        (∑ j ∈ range ((M : ℕ) - 1), ((j + 2 : ℕ) : ℝ) ^ (-(5 / 3 : ℝ))) + 1 ≤ 3 by linarith)


/-! ## The cubic estimate in completion scale -/

/-- Frequency-independent factor left after extracting the pair gcd. -/
def kloostermanCompletionScale (M : ℕ+) (c : ZMod (M : ℕ)) : ℝ :=
  8 * ((M : ℕ).divisors.card : ℝ) * (M : ℝ) ^ (2 / 3 : ℝ) *
    (Nat.gcd (M : ℕ) c.val : ℝ) ^ (1 / 3 : ℝ)

theorem kloostermanCompletionScale_nonneg (M : ℕ+) (c : ZMod (M : ℕ)) :
    0 ≤ kloostermanCompletionScale M c := by
  unfold kloostermanCompletionScale
  positivity

/-- Cube monotonicity converts the composite cubic estimate into its exact completion scale. -/
theorem norm_kloostermanSum_le_completionScale
    (M : ℕ+) (a b c : ZMod (M : ℕ)) :
    ‖kloostermanSum (M : ℕ) a (b * c)‖ ≤
      kloostermanCompletionScale M c *
        (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ) := by
  let g := Nat.gcd (M : ℕ) c.val
  let h := Nat.gcd (M : ℕ) (Nat.gcd a.val b.val)
  have hMpow : ((M : ℝ) ^ (2 / 3 : ℝ)) ^ 3 = (M : ℝ) ^ 2 := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    norm_num
  have hgpow : ((g : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (g : ℝ) := by
    simpa only [one_div] using
      Real.rpow_inv_natCast_pow (n := 3) (Nat.cast_nonneg (α := ℝ) g) (by norm_num)
  have hhpow : ((h : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = (h : ℝ) := by
    simpa only [one_div] using
      Real.rpow_inv_natCast_pow (n := 3) (Nat.cast_nonneg (α := ℝ) h) (by norm_num)
  have hcube : (kloostermanCompletionScale M c * (h : ℝ) ^ (1 / 3 : ℝ)) ^ 3 =
      512 * ((M : ℕ).divisors.card : ℝ) ^ 3 * (M : ℝ) ^ 2 * ((g : ℝ) * (h : ℝ)) := by
    change (8 * ((M : ℕ).divisors.card : ℝ) * (M : ℝ) ^ (2 / 3 : ℝ) *
      (g : ℝ) ^ (1 / 3 : ℝ) * (h : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = _
    simp only [mul_pow, hMpow, hgpow, hhpow]
    norm_num <;> ring
  have hfreq : (Nat.gcd (M : ℕ) (Nat.gcd a.val (b * c).val) : ℝ) ≤
      (g : ℝ) * (h : ℝ) := by
    exact_mod_cast residueFrequencyGcd_le M a b c
  have hbound := (norm_kloostermanSum_cube_le M a (b * c)).trans
    (mul_le_mul_of_nonneg_left hfreq (by positivity))
  rw [← hcube] at hbound
  exact (pow_le_pow_iff_left₀ (norm_nonneg _)
    (mul_nonneg (kloostermanCompletionScale_nonneg M c)
      (Real.rpow_nonneg (Nat.cast_nonneg h) _)) (by norm_num : 3 ≠ 0)).mp hbound

/-- The pair gcd is an actual member of the common-divisor sum. -/
theorem residuePairGcd_rpow_le_divisor_sum (M : ℕ+) (a b : ZMod (M : ℕ)) :
    (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ) ≤
      ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        if d.val ∣ a.val ∧ d.val ∣ b.val then (d.val : ℝ) ^ (1 / 3 : ℝ) else 0 := by
  classical
  let g := Nat.gcd (M : ℕ) (Nat.gcd a.val b.val)
  have hg : g ∈ (M : ℕ).divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _, M.pos.ne'⟩
  have hga : g ∣ a.val := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : g ∣ b.val := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have h := single_le_sum
    (s := univ)
    (f := fun d : {d : ℕ // d ∈ (M : ℕ).divisors} =>
      if d.val ∣ a.val ∧ d.val ∣ b.val then (d.val : ℝ) ^ (1 / 3 : ℝ) else 0)
    (fun _ _ => by split_ifs <;> positivity)
    (mem_univ (⟨g, hg⟩ : {d : ℕ // d ∈ (M : ℕ).divisors}))
  change (if g ∣ a.val ∧ g ∣ b.val then (g : ℝ) ^ (1 / 3 : ℝ) else 0) ≤ _ at h
  rw [if_pos (And.intro hga hgb)] at h
  exact h

/-- Two restricted Fourier masses leave the summable divisor exponent `−5/3`. -/
theorem divisorFrequencyScale_eq (M : ℕ+)
    (d : {d : ℕ // d ∈ (M : ℕ).divisors}) :
    (d.val : ℝ) ^ (1 / 3 : ℝ) * (modulusDivisorQuotient M d : ℝ) ^ 2 =
      (M : ℝ) ^ 2 * (d.val : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hd : (0 : ℝ) < (d.val : ℝ) := by
    exact_mod_cast Nat.pos_of_mem_divisors d.property
  have hq : (modulusDivisorQuotient M d : ℝ) = (M : ℝ) / (d.val : ℝ) := by
    apply (eq_div_iff hd.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors d.property)
  rw [hq, div_pow,
    show -(5 / 3 : ℝ) = (1 / 3 : ℝ) - (2 : ℝ) by norm_num,
    Real.rpow_sub_natCast hd.ne' (1 / 3 : ℝ) 2]
  ring


/-- Two interval transforms weighted by their actual common frequency gcd. -/
def intervalPairGcdFourierMass (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
      ‖intervalAdditiveFourier M A L a‖ * ‖intervalAdditiveFourier M B H b‖ *
        (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ)

/-- The pair-gcd budget follows from two exact divisor-frequency restrictions. -/
theorem intervalPairGcdFourierMass_le (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) :
    intervalPairGcdFourierMass M A L B H ≤
      3 * (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2 := by
  classical
  have hλ : 0 ≤ 1 + Real.log (M : ℝ) := by
    have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.succ_le_of_lt M.pos
    have := Real.log_nonneg hM
    linarith
  have hdivsum :
      (∑ d : {d : ℕ // d ∈ (M : ℕ).divisors}, (d.val : ℝ) ^ (-(5 / 3 : ℝ))) ≤ 3 := by
    rw [← sum_subtype (M : ℕ).divisors (by simp)
      (fun d : ℕ => (d : ℝ) ^ (-(5 / 3 : ℝ)))]
    exact sum_divisors_rpow_neg_five_thirds_le M
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
          ‖intervalAdditiveFourier M A L a‖ * ‖intervalAdditiveFourier M B H b‖ *
            ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
              if d.val ∣ a.val ∧ d.val ∣ b.val then (d.val : ℝ) ^ (1 / 3 : ℝ) else 0 := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (residuePairGcd_rpow_le_divisor_sum M a b)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (d.val : ℝ) ^ (1 / 3 : ℝ) *
          intervalDivisorFourierMass M d A L * intervalDivisorFourierMass M d B H := by
      simp only [mul_sum]
      simp_rw [sum_comm
        (s := univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0))
        (t := (univ : Finset {d : ℕ // d ∈ (M : ℕ).divisors}))]
      apply sum_congr rfl
      intro d _
      rw [mul_assoc, intervalDivisorFourierMass, intervalDivisorFourierMass,
        sum_mul_sum]
      simp only [mul_sum, sum_filter]
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      by_cases hda : d.val ∣ a.val
      · simp only [ha, not_false_eq_true, hda, true_and, and_true, if_true]
        apply sum_congr rfl
        intro b _
        by_cases hb : b = 0 <;> by_cases hdb : d.val ∣ b.val <;>
          simp [hb, hdb, mul_assoc, mul_comm, mul_left_comm]
      · simp [ha, hda]
    _ ≤ ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors},
        (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2 *
          (d.val : ℝ) ^ (-(5 / 3 : ℝ)) := by
      apply sum_le_sum
      intro d _
      have hm := mul_le_mul
        (intervalDivisorFourierMass_le M d A L)
        (intervalDivisorFourierMass_le M d B H)
        (intervalDivisorFourierMass_nonneg M d B H)
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (modulusDivisorQuotient M d : ℝ)) hλ)
      calc
        _ = (d.val : ℝ) ^ (1 / 3 : ℝ) *
            (intervalDivisorFourierMass M d A L * intervalDivisorFourierMass M d B H) := by ring
        _ ≤ (d.val : ℝ) ^ (1 / 3 : ℝ) *
            (((modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ))) *
              ((modulusDivisorQuotient M d : ℝ) * (1 + Real.log (M : ℝ)))) :=
          mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        _ = ((d.val : ℝ) ^ (1 / 3 : ℝ) * (modulusDivisorQuotient M d : ℝ) ^ 2) *
            (1 + Real.log (M : ℝ)) ^ 2 := by ring
        _ = _ := by rw [divisorFrequencyScale_eq]; ring
    _ = (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2 *
        ∑ d : {d : ℕ // d ∈ (M : ℕ).divisors}, (d.val : ℝ) ^ (-(5 / 3 : ℝ)) := by
      rw [mul_sum]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hdivsum
        (mul_nonneg (sq_nonneg (M : ℝ)) (sq_nonneg (1 + Real.log (M : ℝ))))
      exact h.trans_eq (by ring)

/-! ## The exact axes and the rectangle error -/

/-- Separate the zero frequency from a finite cyclic sum. -/
theorem sum_zmod_eq_zero_add_nonzero (M : ℕ+) (f : ZMod (M : ℕ) → ℂ) :
    (∑ a : ZMod (M : ℕ), f a) =
      f 0 + ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0), f a := by
  classical
  calc
    _ = ∑ a : ZMod (M : ℕ),
        ((if a = 0 then f 0 else 0) + (if a ≠ 0 then f a else 0)) := by
      apply sum_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    _ = _ := by simp [sum_add_distrib, sum_filter]

/-- A double finite sum splits into its origin, two axes, and remaining rectangle. -/
theorem sum_zmod_split_axes (M : ℕ+) (f : ZMod (M : ℕ) → ZMod (M : ℕ) → ℂ) :
    (∑ a : ZMod (M : ℕ), ∑ b : ZMod (M : ℕ), f a b) =
      f 0 0 +
        (∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0), f 0 b) +
        (∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0), f a 0) +
        ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
          ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0), f a b := by
  rw [sum_zmod_eq_zero_add_nonzero M]
  simp_rw [sum_zmod_eq_zero_add_nonzero M]
  rw [sum_add_distrib]
  ring

/-- One term of the double Fourier completion of the inverse graph. -/
def rectangleFrequencyTerm
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c a b : ZMod (M : ℕ)) : ℂ :=
  intervalAdditiveFourier M A L a * intervalAdditiveFourier M B H b *
    kloostermanSum (M : ℕ) a (b * c)

def rectangleRowAxis
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) : ℂ :=
  ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
    rectangleFrequencyTerm M A L B H c 0 b

def rectangleColumnAxis
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) : ℂ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    rectangleFrequencyTerm M A L B H c a 0

def rectangleInterior
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) : ℂ :=
  ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
    ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
      rectangleFrequencyTerm M A L B H c a b

/-- Removing the origin leaves exactly the two axes and the nonzero-frequency rectangle. -/
theorem modularInverseRectangleCount_deviation
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    (M : ℂ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℂ) -
        (Nat.totient (M : ℕ) : ℂ) * (L : ℂ) * (H : ℂ) =
      rectangleRowAxis M A L B H c + rectangleColumnAxis M A L B H c +
        rectangleInterior M A L B H c := by
  have hzero : rectangleFrequencyTerm M A L B H c 0 0 =
      (Nat.totient (M : ℕ) : ℂ) * (L : ℂ) * (H : ℂ) := by
    simp only [rectangleFrequencyTerm, intervalAdditiveFourier_zero,
      zero_mul, kloostermanSum_zero_zero]
    ring
  rw [modularInverseRectangleCount_fourier]
  change (∑ a : ZMod (M : ℕ), ∑ b : ZMod (M : ℕ),
      rectangleFrequencyTerm M A L B H c a b) - _ = _
  rw [sum_zmod_split_axes, hzero]
  dsimp only [rectangleRowAxis, rectangleColumnAxis, rectangleInterior]
  ring

/-- The first axis keeps the target gcd and the first interval length. -/
theorem norm_rectangleRowAxis_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    ‖rectangleRowAxis M A L B H c‖ ≤
      (L : ℝ) * (Nat.gcd (M : ℕ) c.val : ℝ) *
        (((M : ℕ).divisors.card : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ))) := by
  calc
    _ ≤ ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
        ‖rectangleFrequencyTerm M A L B H c 0 b‖ := norm_sum_le _ _
    _ = ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
        (L : ℝ) * ‖intervalAdditiveFourier M B H b‖ *
          ‖kloostermanSum (M : ℕ) 0 (b * c)‖ := by
      apply sum_congr rfl
      intro b _
      simp only [rectangleFrequencyTerm, intervalAdditiveFourier_zero,
        norm_mul, Complex.norm_natCast]
    _ ≤ ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
        (L : ℝ) * ‖intervalAdditiveFourier M B H b‖ *
          ((Nat.gcd (M : ℕ) c.val : ℝ) * (Nat.gcd (M : ℕ) b.val : ℝ)) := by
      apply sum_le_sum
      intro b _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      rw [kloostermanSum_comm (M : ℕ) 0 (b * c)]
      refine (norm_kloostermanSum_axis_le_gcd M (b * c)).trans ?_
      exact_mod_cast (show Nat.gcd (M : ℕ) (b * c).val ≤
          Nat.gcd (M : ℕ) c.val * Nat.gcd (M : ℕ) b.val from by
        simpa only [ZMod.val_zero, Nat.gcd_zero_left] using residueFrequencyGcd_le M 0 b c)
    _ = (L : ℝ) * (Nat.gcd (M : ℕ) c.val : ℝ) * intervalGcdFourierMass M B H := by
      rw [intervalGcdFourierMass, mul_sum]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (intervalGcdFourierMass_le M B H) (by positivity)

/-- The second axis keeps the second interval length. -/
theorem norm_rectangleColumnAxis_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    ‖rectangleColumnAxis M A L B H c‖ ≤
      (H : ℝ) * (((M : ℕ).divisors.card : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ))) := by
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ‖rectangleFrequencyTerm M A L B H c a 0‖ := norm_sum_le _ _
    _ = ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ‖intervalAdditiveFourier M A L a‖ * (H : ℝ) *
          ‖kloostermanSum (M : ℕ) a 0‖ := by
      apply sum_congr rfl
      intro a _
      simp only [rectangleFrequencyTerm, intervalAdditiveFourier_zero,
        zero_mul, norm_mul, Complex.norm_natCast]
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ‖intervalAdditiveFourier M A L a‖ * (H : ℝ) * (Nat.gcd (M : ℕ) a.val : ℝ) := by
      apply sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (norm_kloostermanSum_axis_le_gcd M a)
        (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    _ = (H : ℝ) * intervalGcdFourierMass M A L := by
      rw [intervalGcdFourierMass, mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (intervalGcdFourierMass_le M A L) (Nat.cast_nonneg _)

/-- The cubic estimate and two divisor restrictions control every nonzero-frequency term. -/
theorem norm_rectangleInterior_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    ‖rectangleInterior M A L B H c‖ ≤
      kloostermanCompletionScale M c * (3 * (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2) := by
  calc
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ‖∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
          rectangleFrequencyTerm M A L B H c a b‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
          ‖rectangleFrequencyTerm M A L B H c a b‖ := by
      apply sum_le_sum
      intro a _
      exact norm_sum_le _ _
    _ ≤ ∑ a ∈ univ.filter (fun a : ZMod (M : ℕ) => a ≠ 0),
        ∑ b ∈ univ.filter (fun b : ZMod (M : ℕ) => b ≠ 0),
          kloostermanCompletionScale M c *
            (‖intervalAdditiveFourier M A L a‖ * ‖intervalAdditiveFourier M B H b‖ *
              (Nat.gcd (M : ℕ) (Nat.gcd a.val b.val) : ℝ) ^ (1 / 3 : ℝ)) := by
      apply sum_le_sum
      intro a _
      apply sum_le_sum
      intro b _
      simp only [rectangleFrequencyTerm, norm_mul]
      have h := mul_le_mul_of_nonneg_left (norm_kloostermanSum_le_completionScale M a b c)
        (mul_nonneg (norm_nonneg (intervalAdditiveFourier M A L a))
          (norm_nonneg (intervalAdditiveFourier M B H b)))
      exact h.trans_eq (by ring)
    _ = kloostermanCompletionScale M c * intervalPairGcdFourierMass M A L B H := by
      simp only [intervalPairGcdFourierMass, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (intervalPairGcdFourierMass_le M A L B H)
      (kloostermanCompletionScale_nonneg M c)

/-- Uniform finite modular-inverse rectangle estimate, with all endpoints and target gcds retained. -/
theorem modularInverseRectangleCount_error_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    |(modularInverseRectangleCount M A L B H c : ℝ) -
        (Nat.totient (M : ℕ) : ℝ) * (L : ℝ) * (H : ℝ) / (M : ℝ) ^ 2| ≤
      24 * ((M : ℕ).divisors.card : ℝ) * (M : ℝ) ^ (2 / 3 : ℝ) *
          (Nat.gcd (M : ℕ) c.val : ℝ) ^ (1 / 3 : ℝ) * (1 + Real.log (M : ℝ)) ^ 2 +
        ((M : ℕ).divisors.card : ℝ) * (1 + Real.log (M : ℝ)) *
          ((L : ℝ) * (Nat.gcd (M : ℕ) c.val : ℝ) + (H : ℝ)) / (M : ℝ) := by
  have hM : (0 : ℝ) < (M : ℝ) := by exact_mod_cast M.pos
  have hscaled :
      ‖(M : ℂ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℂ) -
          (Nat.totient (M : ℕ) : ℂ) * (L : ℂ) * (H : ℂ)‖ ≤
        (L : ℝ) * (Nat.gcd (M : ℕ) c.val : ℝ) *
            (((M : ℕ).divisors.card : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ))) +
          (H : ℝ) * (((M : ℕ).divisors.card : ℝ) * (M : ℝ) * (1 + Real.log (M : ℝ))) +
          kloostermanCompletionScale M c *
            (3 * (M : ℝ) ^ 2 * (1 + Real.log (M : ℝ)) ^ 2) := by
    rw [modularInverseRectangleCount_deviation]
    have hfirst := norm_add_le
      (rectangleRowAxis M A L B H c + rectangleColumnAxis M A L B H c)
      (rectangleInterior M A L B H c)
    have hsecond := norm_add_le (rectangleRowAxis M A L B H c)
      (rectangleColumnAxis M A L B H c)
    have hr := norm_rectangleRowAxis_le M A L B H c
    have hc := norm_rectangleColumnAxis_le M A L B H c
    have hi := norm_rectangleInterior_le M A L B H c
    linarith only [hfirst, hsecond, hr, hc, hi]
  have he :
      (M : ℝ) ^ 2 * ((modularInverseRectangleCount M A L B H c : ℝ) -
          (Nat.totient (M : ℕ) : ℝ) * (L : ℝ) * (H : ℝ) / (M : ℝ) ^ 2) =
        (M : ℝ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℝ) -
          (Nat.totient (M : ℕ) : ℝ) * (L : ℝ) * (H : ℝ) := by
    field_simp [hM.ne'] <;> ring
  have hcast :
      (M : ℂ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℂ) -
          (Nat.totient (M : ℕ) : ℂ) * (L : ℂ) * (H : ℂ) =
        (((M : ℝ) ^ 2 * (modularInverseRectangleCount M A L B H c : ℝ) -
          (Nat.totient (M : ℕ) : ℝ) * (L : ℝ) * (H : ℝ) : ℝ) : ℂ) := by
    push_cast <;> rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, ← he, abs_mul,
    abs_of_nonneg (sq_nonneg (M : ℝ))] at hscaled
  have hdivide := (le_div_iff₀ (sq_pos_of_pos hM)).mpr
    (show |(modularInverseRectangleCount M A L B H c : ℝ) -
        (Nat.totient (M : ℕ) : ℝ) * (L : ℝ) * (H : ℝ) / (M : ℝ) ^ 2| * (M : ℝ) ^ 2 ≤ _ by
      simpa only [mul_comm] using hscaled)
  refine hdivide.trans_eq ?_
  unfold kloostermanCompletionScale
  field_simp [hM.ne'] <;> ring

/-! ## The literal set of interval pairs -/

/-- Interval-index pairs whose first residue is a unit and whose product is `c`. -/
def modularInverseRectanglePairs
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) : Finset (ℕ × ℕ) :=
  ((range L).product (range H)).filter (fun t : ℕ × ℕ =>
    IsUnit ((A : ZMod (M : ℕ)) + (t.1 : ZMod (M : ℕ))) ∧
      ((A : ZMod (M : ℕ)) + (t.1 : ZMod (M : ℕ))) *
        ((B : ZMod (M : ℕ)) + (t.2 : ZMod (M : ℕ))) = c)

/-- One unit residue selects a Cartesian product of the two interval fibres. -/
def modularInverseRectangleFiber
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ))
    (u : (ZMod (M : ℕ))ˣ) : Finset (ℕ × ℕ) :=
  ((range L).filter (fun j : ℕ =>
    (A : ZMod (M : ℕ)) + (j : ZMod (M : ℕ)) = (u : ZMod (M : ℕ)))).product
    ((range H).filter (fun k : ℕ =>
      (B : ZMod (M : ℕ)) + (k : ZMod (M : ℕ)) = c * (↑u⁻¹ : ZMod (M : ℕ))))

/-- Unit fibres cover exactly the interval pairs satisfying the modular product equation. -/
theorem modularInverseRectanglePairs_eq_biUnion
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    modularInverseRectanglePairs M A L B H c =
      univ.biUnion (modularInverseRectangleFiber M A L B H c) := by
  classical
  ext t
  simp only [modularInverseRectanglePairs, modularInverseRectangleFiber,
    mem_filter, mem_product, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hj, hk⟩, hu, hprod⟩
    refine ⟨hu.unit, ⟨hj, hu.unit_spec.symm⟩, hk, ?_⟩
    have hxy : (hu.unit : ZMod (M : ℕ)) *
        ((B : ZMod (M : ℕ)) + (t.2 : ZMod (M : ℕ))) = c := by
      simpa only [hu.unit_spec] using hprod
    have hinv : (hu.unit : ZMod (M : ℕ)) * (↑hu.unit⁻¹ : ZMod (M : ℕ)) = 1 := by simp
    linear_combination (↑hu.unit⁻¹ : ZMod (M : ℕ)) * hxy -
      ((B : ZMod (M : ℕ)) + (t.2 : ZMod (M : ℕ))) * hinv
  · rintro ⟨u, ⟨hj, hx⟩, hk, hy⟩
    refine ⟨⟨hj, hk⟩, ?_, ?_⟩
    · rw [hx]
      exact u.isUnit
    · rw [hx, hy]
      calc
        _ = c * ((u : ZMod (M : ℕ)) * (↑u⁻¹ : ZMod (M : ℕ))) := by ring
        _ = c := by simp

/-- Disjoint unit fibres identify the multiplicity formula with the literal pair cardinality. -/
theorem modularInverseRectangleCount_eq_card_pairs
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    modularInverseRectangleCount M A L B H c =
      (modularInverseRectanglePairs M A L B H c).card := by
  classical
  symm
  rw [modularInverseRectanglePairs_eq_biUnion, card_biUnion]
  · rw [modularInverseRectangleCount]
    apply sum_congr rfl
    intro u _
    rw [modularInverseRectangleFiber, card_product]
    rfl
  · intro u _ v _ huv
    apply disjoint_left.mpr
    intro t htu htv
    simp only [modularInverseRectangleFiber, mem_product, mem_filter] at htu htv
    exact huv (Units.ext (htu.1.2.symm.trans htv.1.2))

/-- The rectangle estimate for the cardinality of the actual finite interval-pair set. -/
theorem modularInverseRectanglePairs_error_le
    (M : ℕ+) (A : ℤ) (L : ℕ) (B : ℤ) (H : ℕ) (c : ZMod (M : ℕ)) :
    |((modularInverseRectanglePairs M A L B H c).card : ℝ) -
        (Nat.totient (M : ℕ) : ℝ) * (L : ℝ) * (H : ℝ) / (M : ℝ) ^ 2| ≤
      24 * ((M : ℕ).divisors.card : ℝ) * (M : ℝ) ^ (2 / 3 : ℝ) *
          (Nat.gcd (M : ℕ) c.val : ℝ) ^ (1 / 3 : ℝ) * (1 + Real.log (M : ℝ)) ^ 2 +
        ((M : ℕ).divisors.card : ℝ) * (1 + Real.log (M : ℝ)) *
          ((L : ℝ) * (Nat.gcd (M : ℕ) c.val : ℝ) + (H : ℝ)) / (M : ℝ) := by
  rw [← modularInverseRectangleCount_eq_card_pairs]
  exact modularInverseRectangleCount_error_le M A L B H c

end
end GaloisForLFunctions.Goldbach

#print axioms GaloisForLFunctions.Goldbach.residueEdge_pos_iff
#print axioms GaloisForLFunctions.Goldbach.intervalAdditiveFourier_zero
#print axioms GaloisForLFunctions.Goldbach.intervalAdditiveFourier_eq_phase_mul_geometric
#print axioms GaloisForLFunctions.Goldbach.norm_stdAddChar_chord_eq
#print axioms GaloisForLFunctions.Goldbach.residueEdge_le_stdAddChar_chord
#print axioms GaloisForLFunctions.Goldbach.norm_stdAddChar_neg_chord_eq
#print axioms GaloisForLFunctions.Goldbach.norm_intervalAdditiveFourier_le
#print axioms GaloisForLFunctions.Goldbach.norm_intervalAdditiveFourier_eq_prefix
#print axioms GaloisForLFunctions.Goldbach.intervalNonzeroFourierMass_le
#print axioms GaloisForLFunctions.Goldbach.finEquiv_symm_val
#print axioms GaloisForLFunctions.Goldbach.divisorFrequencyEquiv_apply
#print axioms GaloisForLFunctions.Goldbach.intervalAdditiveFourier_divisorFrequency
#print axioms GaloisForLFunctions.Goldbach.intervalDivisorFourierMass_eq
#print axioms GaloisForLFunctions.Goldbach.intervalDivisorFourierMass_le
#print axioms GaloisForLFunctions.Goldbach.kloostermanSum_axis_eq_ramanujan
#print axioms GaloisForLFunctions.Goldbach.kloostermanSum_unit_zero_eq_moebius
#print axioms GaloisForLFunctions.Goldbach.norm_kloostermanSum_unit_zero_le
#print axioms GaloisForLFunctions.Goldbach.norm_kloostermanSum_axis_le_gcd
#print axioms GaloisForLFunctions.Goldbach.gcd_product_dvd_gcd_product
#print axioms GaloisForLFunctions.Goldbach.frequencyGcd_dvd
#print axioms GaloisForLFunctions.Goldbach.residueFrequencyGcd_le
#print axioms GaloisForLFunctions.Goldbach.intervalResidueMultiplicity_fourier
#print axioms GaloisForLFunctions.Goldbach.modularInverseRectangleCount_fourier
#print axioms GaloisForLFunctions.Goldbach.intervalDivisorFourierMass_nonneg
#print axioms GaloisForLFunctions.Goldbach.residueGcd_le_divisor_sum
#print axioms GaloisForLFunctions.Goldbach.intervalGcdFourierMass_le
#print axioms GaloisForLFunctions.Goldbach.sum_divisors_rpow_neg_five_thirds_le
#print axioms GaloisForLFunctions.Goldbach.kloostermanCompletionScale_nonneg
#print axioms GaloisForLFunctions.Goldbach.norm_kloostermanSum_le_completionScale
#print axioms GaloisForLFunctions.Goldbach.residuePairGcd_rpow_le_divisor_sum
#print axioms GaloisForLFunctions.Goldbach.divisorFrequencyScale_eq
#print axioms GaloisForLFunctions.Goldbach.intervalPairGcdFourierMass_le
#print axioms GaloisForLFunctions.Goldbach.sum_zmod_eq_zero_add_nonzero
#print axioms GaloisForLFunctions.Goldbach.sum_zmod_split_axes
#print axioms GaloisForLFunctions.Goldbach.modularInverseRectangleCount_deviation
#print axioms GaloisForLFunctions.Goldbach.norm_rectangleRowAxis_le
#print axioms GaloisForLFunctions.Goldbach.norm_rectangleColumnAxis_le
#print axioms GaloisForLFunctions.Goldbach.norm_rectangleInterior_le
#print axioms GaloisForLFunctions.Goldbach.modularInverseRectangleCount_error_le
#print axioms GaloisForLFunctions.Goldbach.modularInverseRectanglePairs_eq_biUnion
#print axioms GaloisForLFunctions.Goldbach.modularInverseRectangleCount_eq_card_pairs
#print axioms GaloisForLFunctions.Goldbach.modularInverseRectanglePairs_error_le
