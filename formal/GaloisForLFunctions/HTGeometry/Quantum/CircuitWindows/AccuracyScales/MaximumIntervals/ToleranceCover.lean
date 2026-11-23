import GaloisForLFunctions.ArithmeticDiscreteness.TheExceptionalValuesHaveSmallHausdorffDimension

/-! # Exceptional tolerances for exponentially many orbit thresholds -/
open Set Filter Metric MeasureTheory MeasureTheory.Measure Real
open scoped ENNReal Topology
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
noncomputable section

/-- At each size the possible critical tolerances are indexed by a gate
budget. This set retains the tolerances approached infinitely often at
every exponential precision. -/
def exceptionalTolerances (h : ℕ → ℕ → ℝ) : Set ℝ :=
  {e | ∀ q : ℕ, ∃ᶠ k : ℕ in atTop, ∃ j < 2^(8*(k+3)),
    |e-h k j| ≤ 1/(2:ℝ)^(q*k)}

private theorem exp_log_two_nat (c k : ℕ) :
    exp (((c:ℝ)*log 2)*k) = (2:ℝ)^(c*k) := by
  rw [show (c:ℝ)*log 2*k=((c*k:ℕ):ℝ)*log 2 by push_cast; ring,
    exp_nat_mul,exp_log (by norm_num : 0 < (2:ℝ))]

/-- Even exponentially many thresholds have a zero-dimensional exceptional
set when the rate of approximation can be arbitrarily large. -/
theorem dimH_exceptionalTolerances (h : ℕ → ℕ → ℝ) :
    dimH (exceptionalTolerances h) = 0 := by
  apply le_antisymm ?_ bot_le
  apply dimH_le
  intro d hd
  by_contra hle
  have hs : 0 < (d:ℝ) := by
    have hh : (0:ℝ≥0∞) < (d:ℝ≥0∞) := lt_of_not_ge hle
    exact_mod_cast hh
  obtain ⟨q,hq⟩ := exists_nat_gt (8/(d:ℝ))
  let a := 8*log 2
  let b := (q:ℝ)*log 2
  let r (k : ℕ) := exp (-b*(k:ℝ))
  let C := (2:ℝ)^24
  let w (k : ℕ) := (C*2^(d:ℝ))*exp ((a-b*d)*(k:ℝ))
  have hlog := log_pos (by norm_num : 1 < (2:ℝ))
  have hq' : 8 < (q:ℝ)*d := (div_lt_iff₀ hs).mp hq
  have hb : 0 < b := mul_pos (lt_trans (div_pos (by norm_num) hs) hq) hlog
  have hn : a-b*d < 0 := by
    dsimp only [a,b]
    nlinarith only [mul_lt_mul_of_pos_right hq' hlog]
  have hrmono : Antitone r := fun _ _ hkj => exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left (by exact_mod_cast hkj) (neg_nonpos.mpr hb.le))
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have hz := tendsto_pow_atTop_nhds_zero_of_lt_one (exp_pos (-b)).le
      (exp_lt_one_iff.mpr (neg_neg_of_pos hb))
    simpa only [r,mul_comm (-b),exp_nat_mul] using hz
  have hsum : Summable w := by
    have hz := (summable_geometric_of_lt_one (exp_pos (a-b*d)).le
      (exp_lt_one_iff.mpr hn)).mul_left (C*2^(d:ℝ))
    simpa only [w,mul_comm (a-b*d),exp_nat_mul] using hz
  let G (k : ℕ) := Finset.range (2^(8*(k+3)))
  have hcost (k : ℕ) : ((G k).card:ℝ)*(2*r k)^(d:ℝ) ≤ w k := by
    have hc : ((G k).card:ℝ) = C*exp (a*(k:ℝ)) := by
      dsimp only [G,C,a]
      have hh := exp_log_two_nat 8 k
      norm_num only [Nat.cast_ofNat] at hh
      rw [Finset.card_range,Nat.cast_pow,Nat.cast_ofNat,hh,
        show 8*(k+3)=24+8*k by omega,pow_add]
    apply le_of_eq
    rw [hc]
    dsimp only [w,r]
    rw [mul_rpow (by norm_num : 0 ≤ (2:ℝ)) (exp_pos _).le,← exp_mul,
      show C*exp (a*(k:ℝ))*(2^(d:ℝ)*exp (-b*k*d)) =
        (C*2^(d:ℝ))*(exp (a*k)*exp (-b*k*d)) by ring,← exp_add]
    congr 2
    ring
  have hz := ArithmeticDiscreteness.hausdorffMeasure_eq_zero_of_tail_covers
    (Complex.ofReal '' exceptionalTolerances h) G (fun k j => (h k j:ℂ)) r w (d:ℝ) hs
    (fun k => (exp_pos _).le) hrmono hrlim (fun k => by dsimp [w,C]; positivity) hsum hcost (by
      rintro n _ ⟨e,he,rfl⟩
      obtain ⟨k,hk,j,hj,hnear⟩ := frequently_atTop.mp (he q) n
      refine mem_iUnion₂.mpr ⟨k,hk,mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr hj,?_⟩⟩
      rw [mem_closedBall,Complex.isometry_ofReal.dist_eq,Real.dist_eq]
      simpa only [r,b,neg_mul,exp_neg,exp_log_two_nat,one_div] using hnear)
  rw [Complex.isometry_ofReal.hausdorffMeasure_image (Or.inl hs.le)] at hz
  exact ENNReal.zero_ne_top (hz.symm.trans hd)

#print axioms dimH_exceptionalTolerances
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.MaximumIntervals
