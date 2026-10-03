import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthAtomGapCooling
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthMixedPairPolynomial
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthDominantCubic
/-! Exact mixed point-and-ray moments and their gap coefficient identities. -/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section

private def mixedAnchor (q : ℝ) : ℝ :=
  q ^ 2 * 98415 +
      (q ^ 3 * 393660 +
        (q ^ 4 * (1541835/2) +
          (q ^ 5 * 987795 +
            (q ^ 6 * (7468605/8) +
              (q ^ 7 * 695466 +
                (q ^ 8 * (14811093/32) +
                  (q ^ 9 * (3340035/16) +
                    (q ^ 10 * (-2113371/32) +
                      (q ^ 11 * (-897885/8) +
                        (q ^ 12 * (-130977/2) +
                          (q ^ 13 * (-19683/2) +
                            (q ^ 14 * (54675/2) +
                              (q ^ 15 * 8748 + 0)))))))))))))

private def mixedAnchorSlope (q : ℝ) : ℝ :=
  q ^ 2 * (-590490) +
      (q ^ 3 * (-2263545) +
        (q ^ 4 * (-4264650) +
          (q ^ 5 * (-10552275/2) +
            (q ^ 6 * (-19322145/4) +
              (q ^ 7 * (-27969543/8) +
                (q ^ 8 * (-2086398) +
                  (q ^ 9 * (-37753209/32) +
                    (q ^ 10 * (-3033369/4) +
                      (q ^ 11 * (-4434507/32) +
                        (q ^ 12 * (598023/8) +
                          (q ^ 13 * 147258 +
                            (q ^ 14 * (387099/2) +
                              (q ^ 15 * (-41553/2) +
                                (q ^ 16 * (-26244) + 0))))))))))))))

private theorem mixedAnchor_numerator_eq (q : ℝ) : growthNumerator q 3=mixedAnchor q := by
  unfold growthNumerator mixedAnchor
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

private theorem mixedAnchor_slope_eq (q : ℝ) : slopeNumerator q 3=mixedAnchorSlope q := by
  unfold slopeNumerator mixedAnchorSlope
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

def mixedPairMomentPolynomial (q d : ℝ) (j : ℕ) : ℝ :=
  4*(d+1)*(d+3)^j*q^(j+2)+
    ((21/2)*d+9/2)*q*(∑ i ∈ Finset.range (j+1),
      (j.choose i:ℝ)*(d+3)^(j-i)*(i.factorial:ℝ)*q^(j-i))+
    (27/4)*d*(∑ i ∈ Finset.range (j+1),
      (j.choose i:ℝ)*(d+3)^(j-i)*((i+1).factorial:ℝ)*q^(j-i))

def mixedPairMomentCoeff (q : ℝ) (j k : ℕ) : ℝ :=
  4*(((j+1).choose k:ℝ)*11^(j+1-k)-2*(j.choose k:ℝ)*11^(j-k))*q^(j+2)+
    q*(∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*(i.factorial:ℝ)*
      ((21/2)*((j-i+1).choose k:ℝ)*11^(j-i+1-k)-27*((j-i).choose k:ℝ)*11^(j-i-k))*q^(j-i))+
    (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*((i+1).factorial:ℝ)*
      ((27/4)*((j-i+1).choose k:ℝ)*11^(j-i+1-k)-(81/4)*((j-i).choose k:ℝ)*11^(j-i-k))*q^(j-i))

def mixedPairTransferCoeff (q : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    ((growthCoefficient q (i+2)*slopeNumerator q 3-q*growthCoefficientJet q (i+2)*growthNumerator q 3)*
      q^(5-i)*mixedPairMomentCoeff q (i+2) k+
    growthCoefficient q (i+2)*growthNumerator q 3*q^(5-i)*mixedPairMomentCoeff q (i+3) k)

theorem mixedPairMomentPolynomial_0 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 0=
      mixedPairMomentPolynomial q d 0 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_1 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 1=
      mixedPairMomentPolynomial q d 1 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_2 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 2=
      mixedPairMomentPolynomial q d 2 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_3 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 3=
      mixedPairMomentPolynomial q d 3 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_4 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 4=
      mixedPairMomentPolynomial q d 4 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_5 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 5=
      mixedPairMomentPolynomial q d 5 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_6 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 6=
      mixedPairMomentPolynomial q d 6 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_7 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 7=
      mixedPairMomentPolynomial q d 7 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_8 (q d : ℝ) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) 8=
      mixedPairMomentPolynomial q d 8 := by
  norm_num [momentConvolution,polynomialMoment,mixedPairMomentPolynomial,
    Finset.sum_range_succ,Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_eq (q d : ℝ) {j : ℕ} (hj : j ≤ 8) :
    momentConvolution (polynomialMoment q 3) (polynomialMoment q d) j=
      mixedPairMomentPolynomial q d j := by
  interval_cases j
  · exact mixedPairMomentPolynomial_0 q d
  · exact mixedPairMomentPolynomial_1 q d
  · exact mixedPairMomentPolynomial_2 q d
  · exact mixedPairMomentPolynomial_3 q d
  · exact mixedPairMomentPolynomial_4 q d
  · exact mixedPairMomentPolynomial_5 q d
  · exact mixedPairMomentPolynomial_6 q d
  · exact mixedPairMomentPolynomial_7 q d
  · exact mixedPairMomentPolynomial_8 q d

theorem mixedPairMomentPolynomial_gap_expansion_0 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 0=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 0 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_1 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 1=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 1 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_2 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 2=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 2 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_3 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 3=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 3 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_4 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 4=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 4 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_5 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 5=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 5 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_6 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 6=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 6 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_7 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 7=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 7 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion_8 (q v : ℝ) :
    mixedPairMomentPolynomial q (8+v) 8=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q 8 k*v^k := by
  norm_num [mixedPairMomentPolynomial,mixedPairMomentCoeff,Finset.sum_range_succ,
    Nat.choose,Nat.factorial]
  ring

theorem mixedPairMomentPolynomial_gap_expansion (q v : ℝ) (j : ℕ) (hj : j ≤ 8) :
    mixedPairMomentPolynomial q (8+v) j=
      ∑ k ∈ Finset.range 10, mixedPairMomentCoeff q j k*v^k := by
  interval_cases j
  · exact mixedPairMomentPolynomial_gap_expansion_0 q v
  · exact mixedPairMomentPolynomial_gap_expansion_1 q v
  · exact mixedPairMomentPolynomial_gap_expansion_2 q v
  · exact mixedPairMomentPolynomial_gap_expansion_3 q v
  · exact mixedPairMomentPolynomial_gap_expansion_4 q v
  · exact mixedPairMomentPolynomial_gap_expansion_5 q v
  · exact mixedPairMomentPolynomial_gap_expansion_6 q v
  · exact mixedPairMomentPolynomial_gap_expansion_7 q v
  · exact mixedPairMomentPolynomial_gap_expansion_8 q v

def mixedPairTransferNumerator (q d : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 6,
    ((growthCoefficient q (i+2)*slopeNumerator q 3-q*growthCoefficientJet q (i+2)*growthNumerator q 3)*
      q^(5-i)*mixedPairMomentPolynomial q d (i+2)+
    growthCoefficient q (i+2)*growthNumerator q 3*q^(5-i)*mixedPairMomentPolynomial q d (i+3))

theorem momentConvolution_bare_mixed_pair {q : ℝ} (hq : 0 < q) (d : ℝ)
    {j : ℕ} (hj : j ≤ 8) :
    momentConvolution (bareMoment q 3) (bareMoment q d) j=
      mixedPairMomentPolynomial q d j/q^(j+2) := by
  have he (a : ℝ) : polynomialMoment q a=fun i => q^(i+1)*bareMoment q a i := by
    funext i
    rw [bareMoment_eq_polynomial hq.ne']
    field_simp [hq.ne']
  have hp := mixedPairMomentPolynomial_eq q d hj
  rw [he 3,he d,momentConvolution_powerScale] at hp
  apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
  simpa only [Nat.add_assoc,show (1:ℕ)+1=2 by rfl,mul_comm] using hp

theorem growthTransferFunctional_bare_mixed_pair {q : ℝ} (hq : 0 < q) (d : ℝ) :
    growthTransferFunctional q (momentConvolution (bareMoment q 3) (bareMoment q d))=
      mixedPairTransferNumerator q d/q^9 := by
  unfold growthTransferFunctional mixedPairTransferNumerator
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hi5 : i ≤ 5 := by have := Finset.mem_range.mp hi; omega
  rw [momentConvolution_bare_mixed_pair hq d (by omega : i+2 ≤ 8),
    momentConvolution_bare_mixed_pair hq d (by omega : i+3 ≤ 8)]
  interval_cases i <;> norm_num only [Nat.reduceAdd,Nat.reduceSub] <;>
    field_simp [hq.ne']

theorem mixedPairTransferNumerator_gap_expansion (q v : ℝ) :
    mixedPairTransferNumerator q (8+v)=
      ∑ k ∈ Finset.range 10, mixedPairTransferCoeff q k*v^k := by
  unfold mixedPairTransferNumerator mixedPairTransferCoeff
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hi8 : i+3 ≤ 8 := by have := Finset.mem_range.mp hi; omega
  rw [mixedPairMomentPolynomial_gap_expansion q v (i+2) (by omega),
    mixedPairMomentPolynomial_gap_expansion q v (i+3) hi8]
  simp only [Finset.mul_sum,←Finset.sum_add_distrib,add_mul,mul_assoc]

theorem mixedPairTransferCoeff_shift_0 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 0=mixedPairShiftValue 0 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_1 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 1=mixedPairShiftValue 1 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

private def mixedSourceCache2 (y : ℝ) : ℝ :=
  (126082763267172990744328079445/16777216)*y^0+(211381340706861009611337085563/2097152)*y^1+(11159000579939080409603039752803/16777216)*y^2+
    (48860038381206477279316400831943/16777216)*y^3+(20219935058367064220577290821209/2097152)*y^4+(109103690473790397069287448811305/4194304)*y^5+
    (1002634807437172216665815829271767/16777216)*y^6+(2005139794110945359457761001887319/16777216)*y^7+(3516488831209158309837195695095713/16777216)*y^8+
    (2704492916877411199654537830479487/8388608)*y^9+(227662830461280635741062990622781/524288)*y^10+(33528348640611365745553630002027/65536)*y^11+
    (552975068727038347318418896583937/1048576)*y^12+(249612721675131604535548974363015/524288)*y^13+(49411363906564614348753645724131/131072)*y^14+
    (8590136642926751930742665208909/32768)*y^15+(5251379169523333528378386728721/32768)*y^16+(1411688196565247628550641363759/16384)*y^17+
    (83414382001579012543956559521/2048)*y^18+(17314717212618583215125266443/1024)*y^19+(12599870524790526209787115077/2048)*y^20+
    (2002634007947199823067253603/1024)*y^21+(34606699284306554733591675/64)*y^22+(33090248627258845723468839/256)*y^23+
    (6784458410511206910686781/256)*y^24+(590274754543067812645635/128)*y^25+(671527249181414350038)*y^26+
    (321146776303651752399/4)*y^27+(122763582291919045653/16)*y^28+(4506952653413171379/8)*y^29+
    (59656809285284607/2)*y^30+(1013308395850080)*y^31+(16579630973664)*y^32

private theorem mixedSourceCache2_eq (y : ℝ) : mixedPairShiftValue 2 y=mixedSourceCache2 y := by
  norm_num [mixedPairShiftValue,atomGapPolyEval,mixedPairShiftCoeff,mixedSourceCache2,Finset.sum_range_succ]

theorem mixedPairTransferCoeff_shift_2 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 2=mixedPairShiftValue 2 y := by
  rw [mixedSourceCache2_eq]
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope mixedSourceCache2
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_3 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 3=mixedPairShiftValue 3 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_4 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 4=mixedPairShiftValue 4 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_5 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 5=mixedPairShiftValue 5 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_6 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 6=mixedPairShiftValue 6 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_7 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 7=mixedPairShiftValue 7 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_8 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 8=mixedPairShiftValue 8 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor mixedAnchorSlope
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_9 (y : ℝ) :
    mixedPairTransferCoeff (3/2+y) 9=mixedPairShiftValue 9 y := by
  unfold mixedPairTransferCoeff
  simp only [mixedAnchor_numerator_eq,mixedAnchor_slope_eq]
  unfold mixedPairShiftValue atomGapPolyEval
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [mixedPairShiftCoeff,growthCoefficient,growthCoefficientJet,coolingCoefficient,
    coolingCoefficientJet,coolingCoefficientJetTwo]
  unfold mixedPairMomentCoeff
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  unfold mixedAnchor
  ring_nf (config := {mode := .raw})

theorem mixedPairTransferCoeff_shift_eq (y : ℝ) (k : ℕ) (hk : k ≤ 9) :
    mixedPairTransferCoeff (3/2+y) k=mixedPairShiftValue k y := by
  interval_cases k
  · exact mixedPairTransferCoeff_shift_0 y
  · exact mixedPairTransferCoeff_shift_1 y
  · exact mixedPairTransferCoeff_shift_2 y
  · exact mixedPairTransferCoeff_shift_3 y
  · exact mixedPairTransferCoeff_shift_4 y
  · exact mixedPairTransferCoeff_shift_5 y
  · exact mixedPairTransferCoeff_shift_6 y
  · exact mixedPairTransferCoeff_shift_7 y
  · exact mixedPairTransferCoeff_shift_8 y
  · exact mixedPairTransferCoeff_shift_9 y

end
end RHTower.ThetaCuspDefect
