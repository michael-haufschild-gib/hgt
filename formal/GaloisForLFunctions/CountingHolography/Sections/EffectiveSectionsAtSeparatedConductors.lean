import GaloisForLFunctions.CountingHolography.Sections.ConductorUniformPoleQuadrature
import GaloisForLFunctions.CountingHolography.Sections.SmallMultiplicitiesOnSquareConductors

/-!
# Effective sections at separated conductors

The jet debit on the original finite mesh is bounded by squared total variation.
For effective divisors the two pole readings retain a fixed proportion of the
product of the conductor moments. When that product dominates the fourth power
of multiplicity, the full contact modulus fits inside the original real radius.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset MeasureTheory Filter Topology AbsoluteGeometryOfSpecZ

private theorem box_nonnegative (f : ℝ → ℝ) (u v : ℝ) : 0 ≤ boxKernel f u v := by
  rcases (abs_nonneg (u-v)).eq_or_lt with h | h
  · simp only [boxKernel, ← h, archLevyDensity_zero, zero_mul, le_refl]
  exact mul_nonneg (_root_.RHTower.archLevyDensity_pos h).le (sq_nonneg _)

/-- The regularized jet debit has an upper bound on every finite mesh, independent
of the horizon, the resolution and the signs of the coefficients. -/
theorem uniform_finite_jet_debit : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (a : Fin N → ℤ) (L r : ℕ), 0 < r →
      degreeForm (packet a) L r ≤ C * (∑ i, |(a i : ℝ)|)^2 := by
  obtain ⟨B,hB⟩ := tendsto_levyRow_sub_log.bddAbove_range
  obtain ⟨A,hA,hsize⟩ := contactMultiplicity_size
  let D := max B 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D*A, mul_nonneg hD (zero_le_one.trans hA), fun N a L r hr => ?_⟩
  let J := Ioc r (r+L*r)
  let f := packet a
  let mass (j : ℕ) := degreeSample f r j ^ 2 / j
  have hm (j : ℕ) : 0 ≤ mass j := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hh := (le_abs_self _).trans (hsize N a L r 1)
  simp only [contactMultiplicity,Nat.mul_one] at hh
  have he : ∑ j ∈ J, mass j ≤ A * (∑ i, |(a i : ℝ)|)^2 := by
    have heq : (∑ j ∈ J, mass j) = ∑ j ∈ Ioc r (r+L*r), degreeSample (packet a) r j *
        degreeSample (packet a) r j / j := by simp only [mass,f,J,sq]
    rw [← heq] at hh
    linarith only [hh,sum_nonneg (s := J) (fun j _ => hm j)]
  have hd : ∑ j ∈ J, mass j*(levyRow j - Real.log ((j : ℝ)/(2*Real.pi))) ≤ D * ∑ j ∈ J, mass j := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    exact (mul_le_mul_of_nonneg_left ((hB ⟨j,rfl⟩).trans (le_max_left _ _)) (hm j)).trans_eq (mul_comm _ _)
  have hlo : 0 ≤ ∑ j ∈ J, mass j*lowTail r j := sum_nonneg fun j _ => mul_nonneg (hm _) (sum_nonneg
    fun l _ => levyWeight_nonneg l j)
  have hhi : 0 ≤ ∑ j ∈ J, mass j*highTail (r+L*r) j := sum_nonneg fun j _ => mul_nonneg (hm _)
    (tsum_nonneg fun l => levyWeight_nonneg _ _)
  have hbox : 0 ≤ ∑ j ∈ J, ∑ k ∈ J, boxKernel f (Real.log ((j : ℝ)/r))
      (Real.log ((k : ℝ)/r)) / ((j : ℝ)*k) := sum_nonneg fun j _ => sum_nonneg fun k _ =>
    div_nonneg (box_nonnegative _ _ _) (by positivity)
  rw [degreeForm_eq _ _ hr]
  change _ - _ - _ - _ ≤ _
  dsimp only [J,mass,f] at hd hlo hhi hbox he
  linarith only [hd,hlo,hhi,hbox,mul_le_mul_of_nonneg_left he hD]

theorem coefficientVariation_eq_resolution {N : ℕ} (a : Fin N → ℤ) :
    (∑ i, |(a i : ℝ)|) = resolution a := by
  unfold resolution
  rw [Nat.cast_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

private theorem moment_le_resolution {N : ℕ} {t : ℝ} (ht : t ≤ 0) (a : Fin N → ℤ) :
    |conductorExpMoment t a| ≤ resolution a := by
  rw [← coefficientVariation_eq_resolution]
  unfold conductorExpMoment
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  apply mul_le_of_le_one_right (abs_nonneg _)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg ht (Real.log_nonneg (by linarith only [Nat.cast_nonneg (α := ℝ) i.val]))

/-- At the original resolution, every signed divisor has bounded additive error
in each pole reading. The constant is independent of both degree and multiplicity. -/
theorem bounded_actual_pole_reading_error {t : ℝ} (ht : t ≤ 1) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (N : ℕ) (a : Fin N → ℤ), |sampledDegree (packet a) (3*windowEnd N) (resolution a) t -
      unitAtomMoment t * conductorExpMoment t a| ≤ C := by
  obtain ⟨C,hC,h⟩ := conductor_moment_quadrature_error t
  refine ⟨C,hC,fun N a => ?_⟩
  by_cases hz : a = 0
  · subst a
    simpa [resolution,sampledDegree,conductorExpMoment] using hC
  have hr := resolution_pos hz
  have he := h hr a
  have hv : (resolution (fun i => |a i|) : ℝ) = resolution a := by
    rw [← coefficientVariation_eq_resolution (fun i => |a i|), ← coefficientVariation_eq_resolution a]
    simp only [Int.cast_abs,abs_abs]
  have hm := (le_abs_self _).trans (moment_le_resolution (sub_nonpos.mpr ht) (fun i => |a i|))
  rw [hv] at hm
  refine he.trans ((mul_le_mul_of_nonneg_left hm (div_nonneg hC (Nat.cast_nonneg _))).trans_eq ?_)
  exact div_mul_cancel₀ C (Nat.cast_ne_zero.mpr hr.ne')

/-- On all positive-pole-balanced signed divisors the entire finite-mesh pole
correction costs at most a constant times total multiplicity. -/
theorem pole_balanced_linear_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ),
    positivePoleDegree a = 0 → |radius a-jetRadius a| ≤ C*resolution a := by
  obtain ⟨P,hP,hp⟩ := bounded_actual_pole_reading_error (by norm_num : (1/2 : ℝ) ≤ 1)
  obtain ⟨D,hD,hd⟩ := bounded_actual_pole_reading_error (by norm_num : -(1/2 : ℝ) ≤ 1)
  let I := unitAtomMoment (-(1/2))
  have hI : 0 < I := unitAtomMoment_pos _
  refine ⟨2*(I+D)*P,by positivity,fun N a ha => ?_⟩
  by_cases hz : a = 0
  · subst a
    simp [resolution,radius,jetRadius,logRadius,sampledDegree,degreeForm,degreePairing]
  have hf : conductorExpMoment (1/2) a = positivePoleDegree a := by
    unfold conductorExpMoment positivePoleDegree
    refine sum_congr rfl fun i _ => ?_
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos (by positivity)]
    rw [mul_comm (1/2 : ℝ) (Real.log _), mul_comm (a i : ℝ)]
  let S (t : ℝ) := sampledDegree (packet a) (3*windowEnd N) (resolution a) t
  have hp' : |S (1/2)| ≤ P := by simpa only [hf,ha,mul_zero,sub_zero,S] using hp N a
  have hd' : |S (-(1/2))-I*conductorExpMoment (-(1/2)) a| ≤ D := hd N a
  have hr : (1 : ℝ) ≤ resolution a := by exact_mod_cast resolution_pos hz
  have hm : |S (-(1/2))| ≤ (I+D)*resolution a := calc
    _ ≤ |S (-(1/2))-I*conductorExpMoment (-(1/2)) a| + |I*conductorExpMoment (-(1/2)) a| := by
      nth_rw 1 [← sub_add_cancel (S (-(1/2))) (I*conductorExpMoment (-(1/2)) a)]
      exact abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_pos hI]
      linarith only [hd',mul_le_mul_of_nonneg_left (moment_le_resolution (by norm_num : -(1/2 : ℝ) ≤ 0) a) hI.le,
        le_mul_of_one_le_right hD hr]
  have he : radius a-jetRadius a = 2*(S (-(1/2))*S (1/2)) := by
    unfold radius jetRadius logRadius S
    ring
  rw [he,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hp'' := mul_le_mul hm hp' (abs_nonneg _) (mul_nonneg (add_nonneg hI.le hD) (Nat.cast_nonneg _))
  linarith only [hp'']

private theorem moment_nonneg {N : ℕ} {a : Fin N → ℤ} (ha : ∀ i, 0 ≤ a i) (t : ℝ) :
    0 ≤ conductorExpMoment t a :=
  sum_nonneg fun i _ => mul_nonneg (by exact_mod_cast ha i) (Real.exp_pos _).le

private theorem effective_pole_lower (t : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℕ, ∀ {N r : ℕ}, R ≤ r → ∀ a : Fin N → ℤ, (∀ i, 0 ≤ a i) →
      c * conductorExpMoment t a ≤ sampledDegree (packet a) (3*windowEnd N) r t := by
  have hc := half_pos (unitAtomMoment_pos t)
  obtain ⟨R,hR⟩ := uniform_conductor_moment_quadrature t hc
  refine ⟨unitAtomMoment t/2, hc, R, fun {N r} hr a ha => ?_⟩
  have hv := hR hr a
  simp only [abs_of_nonneg (ha _)] at hv
  linarith only [(abs_le.mp hv).1]

private theorem mass_eq_resolution {N : ℕ} {a : Fin N → ℤ} (ha : ∀ i, 0 ≤ a i) :
    (∑ i, (a i : ℝ)) = resolution a := by
  have hn (i : Fin N) : 0 ≤ (a i : ℝ) := by exact_mod_cast ha i
  simpa only [abs_of_nonneg (hn _)] using coefficientVariation_eq_resolution a

/-- A uniform lower bound for the signed degree of an effective divisor on
its actual mesh. It includes all prime powers and both archimedean poles. -/
theorem effective_divisor_degree_lower : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ R : ℕ,
    ∀ {N : ℕ} (a : Fin N → ℤ), (∀ i, 0 ≤ a i) → R ≤ resolution a →
      c * (conductorExpMoment (-(1/2)) a * conductorExpMoment (1/2) a) -
        C*(resolution a : ℝ)^4 ≤ radius a - Real.log (contactModulus a) := by
  obtain ⟨c,hc,Rm,hm⟩ := effective_pole_lower (-(1/2))
  obtain ⟨b,hb,Rp,hp⟩ := effective_pole_lower (1/2)
  obtain ⟨J,hJ,hjet⟩ := uniform_finite_jet_debit
  obtain ⟨U,hU,hord⟩ := ordinary_modulus_quartic
  obtain ⟨V,hV⟩ := effective_modulus_difference_bound
  refine ⟨2*(c*b), J+U+|V|+1, by positivity, by positivity,
    max 1 (max Rm Rp), fun {N} a ha hr => ?_⟩
  let r := resolution a
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hmr := hm ((le_max_left Rm Rp).trans ((le_max_right 1 _).trans hr)) a ha
  have hpr := hp ((le_max_right Rm Rp).trans ((le_max_right 1 _).trans hr)) a ha
  have hmul := mul_le_mul hmr hpr (mul_nonneg hb.le (moment_nonneg ha _))
    ((mul_nonneg hc.le (moment_nonneg ha _)).trans hmr)
  have hj := hjet N a (3*windowEnd N) r hr1
  have ho := hord N a
  have hv := (hV N a ha).2
  have hmass := mass_eq_resolution ha
  have hn (i : Fin N) : 0 ≤ (a i : ℝ) := by exact_mod_cast ha i
  simp only [abs_of_nonneg (hn _),hmass] at hj ho
  rw [hmass] at hv
  have hpow : (r : ℝ)^2 ≤ (r : ℝ)^4 := by
    have : (1:ℝ) ≤ r := by exact_mod_cast hr1
    exact pow_le_pow_right₀ this (by decide)
  have hV' := mul_le_mul_of_nonneg_right (le_abs_self V) (sq_nonneg (r : ℝ))
  have hJ' := mul_le_mul_of_nonneg_left hpow hJ
  have hV'' := mul_le_mul_of_nonneg_left hpow (abs_nonneg V)
  change _ ≤ 2*(_ * _) - degreeForm (packet a) (3*windowEnd N) r - _
  dsimp only [r] at *
  linarith only [hmul,hj,ho,hv,hJ',hV',hV'',sq_nonneg ((resolution a : ℝ)^2)]

private theorem primePair_reading {p : ℕ} (hp : 0 < p) (m : ℕ) (t : ℝ) :
    conductorExpMoment t (m • primePair p) = (m : ℝ)*(Real.exp (t*Real.log p)+1) := by
  have hd : ((p-1 : ℕ) : ℝ)+1 = p := by rw [Nat.cast_sub hp]; push_cast; ring
  unfold conductorExpMoment
  simp only [Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, mul_assoc, ← mul_sum]
  unfold primePair
  simp only [Pi.add_apply, Pi.single_apply,Int.cast_add, Int.cast_ite,Int.cast_one,Int.cast_zero,
    add_mul,ite_mul,one_mul,zero_mul,sum_add_distrib,sum_ite_eq',mem_univ,if_true,
    Fin.val_zero,Nat.cast_zero,zero_add,hd,Real.log_one,mul_zero,Real.exp_zero]

/-- Once multiplicity is sufficiently large, every prescribed conductor above
a fixed multiple of m⁴ has its full integral contact modulus inside its original
radius. The unit multiple of this generator is a nonzero rational section. -/
theorem all_separated_primePair_moduli_fit : ∃ K : ℝ, 0 < K ∧ ∃ R : ℕ,
    ∀ {m p : ℕ}, R ≤ m → 0 < p → K*(m : ℝ)^4 ≤ p →
      Real.log (contactModulus (m • primePair p)) < radius (m • primePair p) ∧
      (1 : ℤ) ∈ smallSections (generator (m • primePair p) : ℝ) (radius (m • primePair p)) := by
  obtain ⟨c,C,hc,hC,R,h⟩ := effective_divisor_degree_lower
  let D := (16*C+1)/c
  have hD : 0 < D := div_pos (by positivity) hc
  refine ⟨D^2, sq_pos_of_pos hD, max 1 R, fun {m p} hm hp hsep => ?_⟩
  let a := m • primePair p
  have ha (i : Fin (p+1)) : 0 ≤ a i := by
    change 0 ≤ (m • primePair p) i
    rw [Pi.smul_apply,nsmul_eq_mul]
    apply mul_nonneg (Int.natCast_nonneg _)
    simp only [primePair,Pi.add_apply,Pi.single_apply]
    split_ifs <;> norm_num
  have hm0 : 0 < m := (le_max_left 1 R).trans hm
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have hr : (resolution a : ℝ) = 2*m := by
    have he := primePair_reading hp m 0
    simp only [conductorExpMoment,zero_mul,Real.exp_zero,mul_one,one_add_one_eq_two] at he
    exact (mass_eq_resolution ha).symm.trans (he.trans (mul_comm _ _))
  have hr' : resolution a = 2*m := by exact_mod_cast hr
  have hR : R ≤ resolution a := by
    rw [hr']
    have hRm := (le_max_right 1 R).trans hm
    omega
  have hq := h a ha hR
  have hs : D*(m : ℝ)^2 ≤ Real.sqrt p := by
    have he : (D*(m : ℝ)^2)^2 ≤ (p : ℝ) := by convert hsep using 1; ring
    simpa only [Real.sqrt_sq (mul_nonneg hD.le (sq_nonneg _))] using Real.sqrt_le_sqrt he
  have hweight : Real.exp ((1/2 : ℝ)*Real.log p) = Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Nat.cast_pos.mpr hp), mul_comm]
  rw [primePair_reading hp m,primePair_reading hp m,hweight,hr] at hq
  have hneg : (m : ℝ) ≤ m*(Real.exp (-(1/2 : ℝ)*Real.log p)+1) := by
    linarith only [mul_nonneg hm'.le (Real.exp_pos (-(1/2 : ℝ)*Real.log p)).le]
  have hpos : (m : ℝ)*Real.sqrt p ≤ m*(Real.sqrt p+1) := by linarith only [hm'.le]
  have hprod := mul_le_mul hneg hpos (mul_nonneg hm'.le (Real.sqrt_nonneg _))
    (mul_nonneg hm'.le (add_nonneg (Real.exp_pos _).le zero_le_one))
  have hD' : c*D = 16*C+1 := by unfold D; field_simp
  have hpay := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (sq_nonneg (m : ℝ))) hc.le
  have he : c*((m : ℝ)^2*(D*m^2)) = (16*C+1)*(m : ℝ)^4 := by rw [← hD']; ring
  rw [he] at hpay
  have hfit : Real.log (contactModulus a) < radius a := by
    linarith only [hq,hpay,mul_le_mul_of_nonneg_left hprod hc.le,pow_pos hm' 4]
  have hg : (generator a : ℝ) = contactModulus a := by exact_mod_cast generator_eq_contactModulus a ha
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  refine ⟨hfit, (mem_smallSections hpos 1).mpr ?_⟩
  rw [Int.cast_one,mul_one,abs_of_pos hpos]
  rw [← hg] at hfit
  exact ((Real.log_lt_iff_lt_exp hpos).mp hfit).le

#print axioms bounded_actual_pole_reading_error
#print axioms pole_balanced_linear_error
#print axioms uniform_finite_jet_debit
#print axioms effective_divisor_degree_lower
#print axioms all_separated_primePair_moduli_fit

end GaloisForLFunctions.CountingHolography.Sections
