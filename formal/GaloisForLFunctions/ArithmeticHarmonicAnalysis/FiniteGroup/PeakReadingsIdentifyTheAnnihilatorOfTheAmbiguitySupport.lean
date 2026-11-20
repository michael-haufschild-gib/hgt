import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.TheSymplecticFourierIdentityOfCyclicAmbiguity

/-!
# Maximal ambiguity readings and minimal support

A displacement gives the maximal reading precisely when it annihilates
every occupied phase-space point under the symplectic pairing. Every
nonzero period-q signal occupies at least q points. Equality holds
exactly when the support equals its symplectic annihilator.
-/
noncomputable section
open Complex Finset
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {q : ℕ} [NeZero q]
local notation "G" => ZMod q × ZMod q
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod q) ℂ)

def symplecticIndex (x y : G) := x.1*y.2-x.2*y.1

def ambiguitySupport (c : ZMod q → ℂ) : Finset G :=
  univ.filter (fun y => 0<cyclicAmbiguityWeight c y.1 y.2)

private theorem weight_nonneg (c : ZMod q → ℂ) (y : G) :
    0≤cyclicAmbiguityWeight c y.1 y.2 := sq_nonneg _

private theorem phase_gap (z : ZMod q) : ‖χ z-1‖^2 = 2*(1-(χ z).re) := by
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_sub,Complex.normSq_one,map_one,mul_one,
    Complex.normSq_eq_norm_sq]
  simp only [ZMod.stdAddChar_apply,Circle.norm_coe,one_pow]
  ring

/-- The deficit from the largest reading is exactly the squared
character error averaged against the original ambiguity weights. -/
theorem ambiguity_peak_defect (c : ZMod q → ℂ) (x : G) :
    (∑ y : G,cyclicAmbiguityWeight c y.1 y.2*‖χ (symplecticIndex x y)-1‖^2) =
      2*(q:ℝ)*(cyclicAmbiguityWeight c 0 0-cyclicAmbiguityWeight c x.1 x.2) := by
  let W (y : G) := cyclicAmbiguityWeight c y.1 y.2
  have hfull : ∑ y : G,W y = (q:ℝ)*cyclicAmbiguityWeight c 0 0 := by
    simpa only [W,Fintype.sum_prod_type,zero_mul,sub_zero,AddChar.map_zero_eq_one,
      Complex.one_re,mul_one] using cyclic_ambiguity_real_fourier c 0 0
  have hcos : ∑ y : G,W y*(χ (symplecticIndex x y)).re=(q:ℝ)*W x := by
    simpa only [W,Fintype.sum_prod_type,symplecticIndex] using cyclic_ambiguity_real_fourier c x.1 x.2
  calc _ = ∑ y : G,(2*W y-2*(W y*(χ (symplecticIndex x y)).re)) := by
         refine sum_congr rfl fun y _ => ?_
         rw [phase_gap]; dsimp only [W]; ring
       _ = _ := by rw [sum_sub_distrib,←mul_sum,←mul_sum,hfull,hcos]; dsimp only [W]; ring

private theorem period_cast_pos : 0 < (q:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))

theorem ambiguity_weight_le_origin (c : ZMod q → ℂ) (x : G) :
    cyclicAmbiguityWeight c x.1 x.2≤cyclicAmbiguityWeight c 0 0 := by
  have h := sum_nonneg (s:=univ) (fun (y : G) _ =>
    mul_nonneg (weight_nonneg c y) (sq_nonneg ‖χ (symplecticIndex x y)-1‖))
  rw [ambiguity_peak_defect] at h
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (mul_pos zero_lt_two (period_cast_pos (q:=q))))

/-- The full set of maximal readings is the annihilator of the
occupied phase-space support, over composite as well as prime moduli. -/
theorem ambiguity_peak_iff_annihilator (c : ZMod q → ℂ) (x : G) :
    cyclicAmbiguityWeight c x.1 x.2=cyclicAmbiguityWeight c 0 0 ↔
      ∀ y ∈ ambiguitySupport c, symplecticIndex x y=0 := by
  have hq : 0 < 2*(q:ℝ) := mul_pos zero_lt_two period_cast_pos
  constructor
  · intro hp y hy
    have hw : 0<cyclicAmbiguityWeight c y.1 y.2 := (mem_filter.mp hy).2
    have h := single_le_sum (f:=fun t : G => cyclicAmbiguityWeight c t.1 t.2*‖χ (symplecticIndex x t)-1‖^2)
      (fun t _ => mul_nonneg (weight_nonneg c t) (sq_nonneg _)) (mem_univ y)
    rw [ambiguity_peak_defect,hp,sub_self,mul_zero] at h
    have hsq := nonpos_of_mul_nonpos_right h hw
    have hz := sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))
    have hχ := sub_eq_zero.mp (norm_eq_zero.mp hz)
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using hχ
  · intro hann
    have hs : (∑ y : G,cyclicAmbiguityWeight c y.1 y.2*‖χ (symplecticIndex x y)-1‖^2)=0 := by
      refine sum_eq_zero fun y _ => ?_
      by_cases h : 0 < cyclicAmbiguityWeight c y.1 y.2
      · simp [hann y (mem_filter.mpr ⟨mem_univ _,h⟩)]
      · rw [le_antisymm (le_of_not_gt h) (weight_nonneg c y),zero_mul]
    rw [ambiguity_peak_defect] at hs
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left hq.ne')).symm

private theorem positive_origin (c : ZMod q → ℂ) (hc : c≠0) :
    0<cyclicAmbiguityWeight c 0 0 := by
  obtain ⟨j,hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra! h; exact hc (funext h)
  have h := single_le_sum (f:=fun x => ‖c x‖^2) (fun _ _ => sq_nonneg _) (mem_univ j)
  rw [cyclic_ambiguity_origin]
  exact sq_pos_of_pos ((sq_pos_of_pos (norm_pos_iff.mpr hj)).trans_le h)

private theorem support_mass (c : ZMod q → ℂ) :
    (∑ y ∈ ambiguitySupport c, cyclicAmbiguityWeight c y.1 y.2)=(q:ℝ)*cyclicAmbiguityWeight c 0 0 := by
  calc _ = ∑ y : G,cyclicAmbiguityWeight c y.1 y.2 := by
         apply sum_subset (subset_univ _)
         intro y _ hn
         exact le_antisymm (le_of_not_gt fun h => hn (mem_filter.mpr ⟨mem_univ _,h⟩)) (weight_nonneg c y)
       _ = _ := by simpa only [Fintype.sum_prod_type,cyclic_ambiguity_origin] using cyclic_ambiguity_total_mass c

/-- A nonzero signal occupies at least one full period of phase-space sites. -/
theorem period_le_ambiguity_support_card (c : ZMod q → ℂ) (hc : c≠0) :
    q≤(ambiguitySupport c).card := by
  have h := sum_le_sum (s:=ambiguitySupport c) (fun y _ => ambiguity_weight_le_origin c y)
  rw [support_mass,sum_const,nsmul_eq_mul] at h
  exact_mod_cast (le_of_mul_le_mul_right h (positive_origin c hc))

/-- Minimal cardinality holds exactly for supports equal to their
symplectic annihilators. On such a support the height is constant. -/
theorem minimal_ambiguity_support_iff (c : ZMod q → ℂ) (hc : c≠0) :
    (ambiguitySupport c).card=q ↔
      ∀ x : G, x ∈ ambiguitySupport c ↔ ∀ y ∈ ambiguitySupport c, symplecticIndex x y=0 := by
  let W (y : G) := cyclicAmbiguityWeight c y.1 y.2
  let M := cyclicAmbiguityWeight c 0 0
  have hm : 0<M := positive_origin c hc
  constructor
  · intro he x
    rw [←ambiguity_peak_iff_annihilator c x]
    constructor
    · intro hx
      have h := single_le_sum (s:=ambiguitySupport c) (f:=fun y => M-W y)
        (fun y _ => sub_nonneg.mpr (ambiguity_weight_le_origin c y)) hx
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,he] at h
      change M-W x ≤ (q:ℝ)*M-∑ y ∈ ambiguitySupport c,cyclicAmbiguityWeight c y.1 y.2 at h
      rw [support_mass,sub_self] at h
      exact le_antisymm (ambiguity_weight_le_origin c x) (sub_nonpos.mp h)
    · intro h
      exact mem_filter.mpr ⟨mem_univ _,h.symm ▸ hm⟩
  · intro h
    have hall (x : G) (hx : x∈ambiguitySupport c) : W x=M :=
      (ambiguity_peak_iff_annihilator c x).mpr ((h x).mp hx)
    have hh := sum_congr (s₁:=ambiguitySupport c) rfl hall
    change (∑ x ∈ ambiguitySupport c,cyclicAmbiguityWeight c x.1 x.2) = ∑ _x ∈ ambiguitySupport c,M at hh
    rw [support_mass,sum_const,nsmul_eq_mul] at hh
    have hn : (q:ℝ)=((ambiguitySupport c).card:ℝ) := mul_right_cancel₀ hm.ne' hh
    exact_mod_cast hn.symm

#print axioms ambiguity_peak_defect
#print axioms ambiguity_peak_iff_annihilator
#print axioms period_le_ambiguity_support_card
#print axioms minimal_ambiguity_support_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
