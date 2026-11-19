import GaloisForLFunctions.SignedArithmeticCorrespondences.GluingIntegerGraphsAtTheirQuotientEndpoints
import GaloisForLFunctions.SignedArithmeticCorrespondences.OppositeSectionsOfTheIntegralGraphGauge
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.LittlewoodOmega

/-!
# Completion of the mixed finite part

Once integral endpoints at the same quotient have been combined, the prime-counting
error acts on their weighted variation. Finite truncations approach the resulting
pairing with an explicit bound on the distance.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open ArithmeticCastelnuovoSeveri Finset _root_.RHTower Filter
open scoped ArithmeticFunction.vonMangoldt NNReal

/-- A sublinear error bound on every support, independent of any fixed zero-free
strip. The prime number theorem is applied after the two divisors have been glued. -/
theorem mixed_height_de_la_vallee_poussin :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤ C * ∑ k ∈ range (N+1),
        |quotientCoefficient X N u b k| * ((k : ℝ)*Real.exp (-c*Real.sqrt (Real.log k))) := by
  obtain ⟨A,c,hc,hA,he⟩ := exists_psi_error_eventually
  obtain ⟨L,hL⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually he)
  let W (k : ℕ) : ℝ≥0 := ⟨(k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)), by positivity⟩
  let B := ∑ k ∈ range L, |psiRemainder k| / (W k : ℝ)
  have hB : 0 ≤ B := sum_nonneg fun k _ => div_nonneg (abs_nonneg _) (W k).coe_nonneg
  have h : ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ (A+B)*(W k : ℝ) := by
    intro k hk
    by_cases hlarge : L ≤ k
    · have hr := hL k hlarge
      rw [psiRemainder,chebyshevPsi_eq_psi]
      exact hr.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (W k).coe_nonneg)
    · have hw : 0 < (W k : ℝ) :=
        mul_pos (Nat.cast_pos.mpr hk) (Real.exp_pos _)
      have hsmall : |psiRemainder k|/(W k : ℝ) ≤ B :=
        single_le_sum (f := fun j => |psiRemainder j|/(W j : ℝ))
          (fun j _ => div_nonneg (abs_nonneg _) (W j).coe_nonneg) (mem_range.mpr (lt_of_not_ge hlarge))
      exact ((div_le_iff₀ hw).mp hsmall).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hw.le)
  exact ⟨c,A+B,hc,add_nonneg hA hB,(mixed_height_budget_iff W ⟨A+B,add_nonneg hA hB⟩).2 h⟩

/-- One constant works for every support and both integer divisors. The variation
is measured after cancellation between all pairs sharing a quotient. -/
theorem mixed_height_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤
      C * ∑ k ∈ range (N+1), |quotientCoefficient X N u b k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  exact ⟨C,hC,(mixed_height_budget_iff
    (fun k => ⟨_, Real.rpow_nonneg (Nat.cast_nonneg k) _⟩) ⟨C,hC⟩).2 hbound⟩

private theorem complete_endpoint_weight (W : ℕ → ℝ≥0) (C : ℝ≥0)
    (hbound : ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ C * (W k:ℝ))
    (a : ℕ → ℝ) (ha : Summable (fun k => |a k| * (W k:ℝ))) :
    Summable (fun k => a k*psiRemainder k) ∧
      |∑' k, a k*psiRemainder k| ≤ C * ∑' k, |a k| * (W k:ℝ) := by
  have hterm (k : ℕ) : ‖a k*psiRemainder k‖ ≤ C * (|a k| * (W k:ℝ)) := by
    rw [Real.norm_eq_abs, abs_mul, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa [psiRemainder,chebyshevPsi] using mul_nonneg C.coe_nonneg (W 0).coe_nonneg
    · exact hbound _ hk
  have hmajor := ha.mul_left (C:ℝ)
  have hsum : Summable (fun k => a k*psiRemainder k) := Summable.of_norm_bounded hmajor hterm
  refine ⟨hsum, ?_⟩
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hsum.norm).trans (hsum.norm.tsum_le_tsum hterm hmajor)

/-- A completed endpoint profile can have infinitely many signed jumps.
The scalar error at the zero abscissa controls its absolutely convergent pairing. -/
theorem completed_endpoint_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ → ℝ,
      Summable (fun k => |a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) →
      Summable (fun k => a k*psiRemainder k) ∧
      |∑' k, a k*psiRemainder k| ≤ C * ∑' k, |a k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  exact ⟨C,hC,complete_endpoint_weight
    (fun k => ⟨_,Real.rpow_nonneg (Nat.cast_nonneg k) _⟩) ⟨C,hC⟩ hbound⟩

/-- The unconditional sublinear prime-counting weight also completes the
actual graph pairing, even when no fixed sublinear power is available. -/
theorem completed_endpoint_de_la_vallee_poussin :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ a : ℕ → ℝ,
      let w := fun k : ℕ => (k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k))
      Summable (fun k => |a k| * w k) → Summable (fun k => a k*psiRemainder k) ∧
        |∑' k, a k*psiRemainder k| ≤ C * ∑' k, |a k| * w k := by
  obtain ⟨c,C,hc,hC,h⟩ := mixed_height_de_la_vallee_poussin
  let W (k : ℕ) : ℝ≥0 := ⟨(k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)),by positivity⟩
  exact ⟨c,C,hc,hC,complete_endpoint_weight W ⟨C,hC⟩ ((mixed_height_budget_iff W ⟨C,hC⟩).1 h)⟩

/-- Distance from a finite integral intersection to a prescribed infinite
endpoint profile. The right side prices only the variation left after gluing.
This gives convergence along every exhaustion approaching the same profile
in weighted variation, with one constant for both supports. -/
theorem distance_to_completed_intersection (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ) (a : ℕ → ℝ),
      Summable (fun k => |a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) →
      let c := quotientCoefficient X N u b
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b - ∑' k, a k*psiRemainder k| ≤
        C * ∑' k, |c k-a k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hpair⟩ := completed_endpoint_budget ε hε
  refine ⟨C,hC,fun X N u b a ha => ?_⟩
  let c := quotientCoefficient X N u b
  have hc {k : ℕ} (hk : k ∉ range (N+1)) : c k = 0 :=
    quotientCoefficient_eq_zero (by simpa only [mem_range,not_lt,Nat.succ_le_iff] using hk) X u b
  have hcw : Summable (fun k => |c k| * (k : ℝ)^(zetaZeroAbscissa+ε)) :=
    summable_of_ne_finset_zero (s := range (N+1)) fun k hk => by simp [hc hk]
  have hce := (hpair c hcw).1
  have hae := (hpair a ha).1
  have hdiff : Summable (fun k => |c k-a k| * (k : ℝ)^(zetaZeroAbscissa+ε)) := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_ (hcw.add ha)
    intro k
    have hdiff : |c k-a k| ≤ |c k|+|a k| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (c k) (-a k)
    simpa only [Pi.add_apply, ← add_mul] using
      mul_le_mul_of_nonneg_right hdiff (Real.rpow_nonneg (Nat.cast_nonneg k) (zetaZeroAbscissa+ε))
  have h := (hpair (fun k => c k-a k) hdiff).2
  have he : (∑' k, c k*psiRemainder k) = ∑ k ∈ range (N+1), c k*psiRemainder k :=
    tsum_eq_sum fun k hk => by simp only [hc hk,zero_mul]
  rw [mixed_height_finite_part]
  change |(∑ k ∈ range (N+1), c k*psiRemainder k) - _| ≤ _
  rw [← he,← hce.tsum_sub hae]
  simpa only [sub_mul] using h

private theorem real_count_at_floor (x : ℝ) : chebyshevPsiReal x = chebyshevPsi ⌊x⌋₊ := by
  rw [chebyshevPsiReal_eq_sum_range,sum_range_succ_vonMangoldt_eq_sum_Icc,chebyshevPsi]

/-- The exact zero-free width measured by unrestricted mixed integral divisors.
At width zero this is the square-root estimate. The single-endpoint converse
retains the original arithmetic error, including the real cut between integers. -/
theorem mixed_height_width_iff {α : ℝ} (hα : 0 ≤ α) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤ C * ∑ k ∈ range (N+1),
        |quotientCoefficient X N u b k| * (k:ℝ)^(1/2+α+ε)) ↔
      zetaZeroAbscissa ≤ 1/2+α := by
  rw [← xiZeroHalfPlaneBound_iff_zetaZeroAbscissa_le hα]
  constructor
  · intro h
    apply xiZeroHalfPlaneBound_of_chebyshevErrorPowerSpectrum hα
    intro ε hε
    obtain ⟨C,hC⟩ := h ε hε
    let a := 1/2+α+ε
    let W (k : ℕ) : ℝ≥0 := ⟨(k:ℝ)^a,Real.rpow_nonneg (Nat.cast_nonneg k) _⟩
    have hk := (mixed_height_budget_iff W C).1 hC
    refine ⟨(C:ℝ)+1,by positivity,fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hm := Nat.floor_le hx0
    have hf := Nat.lt_floor_add_one x
    have hw := Real.rpow_le_rpow (Nat.cast_nonneg _) hm ha
    have hone : 1 ≤ x^a := Real.one_le_rpow hx ha
    have he := hk ⌊x⌋₊ ((Nat.one_le_floor_iff x).2 hx)
    change |chebyshevPsi ⌊x⌋₊ - (⌊x⌋₊:ℝ)| ≤ (C:ℝ)*((⌊x⌋₊:ℕ):ℝ)^a at he
    rw [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub,real_count_at_floor]
    change |chebyshevPsi ⌊x⌋₊ - x| ≤ ((C:ℝ)+1)*x^a
    have hg : |((⌊x⌋₊:ℕ):ℝ)-x| ≤ 1 := by rw [abs_of_nonpos (sub_nonpos.mpr hm)]; linarith
    calc _ ≤ |chebyshevPsi ⌊x⌋₊ - (⌊x⌋₊:ℝ)| + |((⌊x⌋₊:ℕ):ℝ)-x| := abs_sub_le _ _ _
         _ ≤ (C:ℝ)*x^a + x^a := add_le_add (he.trans (mul_le_mul_of_nonneg_left hw C.coe_nonneg)) (hg.trans hone)
         _ = _ := by ring
  · intro h ε hε
    obtain ⟨A,hA,hbound⟩ := chebyshevErrorPowerSpectrum_of_xiZeroHalfPlaneBound hα h ε hε
    let W (k : ℕ) : ℝ≥0 := ⟨(k:ℝ)^(1/2+α+ε),Real.rpow_nonneg (Nat.cast_nonneg k) _⟩
    refine ⟨⟨A,hA⟩,(mixed_height_budget_iff W ⟨A,hA⟩).2 (fun k hk => ?_)⟩
    have he := hbound (k:ℝ) (by exact_mod_cast hk)
    rwa [criticalMellinError_vonMangoldt_eq_chebyshevPsiReal_sub,real_count_at_floor,Nat.floor_natCast] at he

/-- Uniform quantitative estimate for the mixed Weil row with its ordinary
prime source retained. The quotient variation prices the finite places;
the product of the opposite sections prices the real place at the same cut. -/
theorem centeredWeilRow_de_la_vallee_poussin :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ (X N L : ℕ) (u b : ℕ → ℤ),
      |centeredWeilRow X N L u b| ≤ C * (∑ k ∈ range (N+1),
        |quotientCoefficient X N u (farJump X L b) k| * ((k:ℝ)*Real.exp (-c*Real.sqrt (Real.log k)))) +
        ‖jointSection X N L u b‖ / (((L:ℝ)+1)*((L:ℝ)+2)) / 2 := by
  obtain ⟨c,C,hc,hC,hpr⟩ := mixed_height_de_la_vallee_poussin
  refine ⟨c,C,hc,hC,fun X N L u b => ?_⟩
  let E := signedDivisorHeight 1 X N u (upperDivisor N (farJump X L b)) -
    poleProduct X N u (farJump X L b) + fractionalBoundary X N u (farJump X L b)
  have hp := hpr X N u (farJump X L b)
  have hj := jointGraphHeight_bound X N L u b
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at hj
  rw [centeredWeilRow_eq]
  change |jointGraphHeight X N L u b-E| ≤ _
  have ht : |jointGraphHeight X N L u b-E| ≤ |jointGraphHeight X N L u b|+|E| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (jointGraphHeight X N L u b) (-E)
  dsimp only [E] at ht ⊢
  linarith only [ht,hp,hj]

private def effectiveProbe (m : ℕ+) : ℝ :=
  centeredWeilRow 1 m 0 (fun _ => 1) (fun j => if j=(m:ℕ) then 1 else 0)

private theorem probe_at_real_cut {x : ℝ} (M : ℕ) (hx : (M:ℝ)+2 ≤ x) :
    ∃ m : ℕ+, M ≤ (m:ℕ) ∧ Real.sqrt (m:ℕ) ≤ Real.sqrt x ∧ 1 ≤ Real.sqrt x ∧
      |effectiveProbe m+(Chebyshev.psi x-x)| ≤ 1 := by
  have hx1 : 1 ≤ x := by linarith only [hx,Nat.cast_nonneg (α := ℝ) M]
  let m : ℕ+ := ⟨⌊x⌋₊,(Nat.one_le_floor_iff x).2 hx1⟩
  have hm : (m:ℝ) ≤ x := Nat.floor_le (by linarith)
  have hnext : x < (m:ℝ)+1 := Nat.lt_floor_add_one x
  have h1 : 1 ≤ (m:ℝ) := by exact_mod_cast m.pos
  have hpsi : chebyshevPsi (m:ℕ) = Chebyshev.psi x := by
    rw [chebyshevPsi_eq_psi]
    change Chebyshev.psi ((⌊x⌋₊:ℕ):ℝ) = Chebyshev.psi x
    simp only [Chebyshev.psi,Nat.floor_natCast]
  refine ⟨m,Nat.le_floor (by linarith only [hx] : (M:ℝ) ≤ x),Real.sqrt_le_sqrt hm,
    by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx1,?_⟩
  have hden : 1 ≤ 2*(m:ℝ)*((m:ℝ)+1) := by nlinarith only [h1,sq_nonneg (m:ℝ)]
  have hpos : 0 < 2*(m:ℝ)*((m:ℝ)+1) := by linarith
  have hhi := (div_le_one hpos).mpr hden
  have hlo := div_nonneg (by norm_num : (0:ℝ) ≤ 1) hpos.le
  rw [effectiveProbe,centeredWeilRow_single,psiRemainder,hpsi,abs_le]
  constructor <;> linarith only [hm,hnext,hhi,hlo]

/-- The centered ordinary Weil row takes both signs beyond every square-root
multiple at arbitrarily large effective endpoints. The positive dual section
estimate and the prime-counting term both appear in the same normalization. -/
theorem effective_endpoint_oscillations (B : ℝ≥0) (M : ℕ) :
    (∃ m : ℕ+, M ≤ (m:ℕ) ∧ B*Real.sqrt (m:ℕ) <
      centeredWeilRow 1 m 0 (fun _ => 1) (fun j => if j=(m:ℕ) then 1 else 0)) ∧
    (∃ m : ℕ+, M ≤ (m:ℕ) ∧
      centeredWeilRow 1 m 0 (fun _ => 1) (fun j => if j=(m:ℕ) then 1 else 0) < -(B*Real.sqrt (m:ℕ))) := by
  let c := littlewoodConst/14
  let l (x : ℝ) := Real.log (Real.log (Real.log x))
  have hc : 0 < c := div_pos littlewoodConst_pos (by norm_num)
  have ht : Tendsto (fun x : ℝ => c*l x) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop))
  have late := (eventually_ge_atTop ((M:ℝ)+2)).and (ht.eventually_ge_atTop ((B:ℝ)+2))
  obtain ⟨hlo,hhi⟩ := chebyshevPsi_sub_omega_pm_littlewood
  have hprice (x : ℝ) (m : ℕ+) (hx : (B:ℝ)+2 ≤ c*l x) (hs : Real.sqrt (m:ℕ) ≤ Real.sqrt x)
      (h1 : 1 ≤ Real.sqrt x) : B*Real.sqrt (m:ℕ)+1 < c*Real.sqrt x*l x := by
    linarith only [mul_le_mul_of_nonneg_left hs B.coe_nonneg,mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg x),h1]
  constructor
  · obtain ⟨x,hx,hxM,hxB⟩ := (hlo.and_eventually late).exists
    obtain ⟨m,hm,hs,h1,hb⟩ := probe_at_real_cut M hxM
    refine ⟨m,hm,?_⟩
    change Chebyshev.psi x-x < -(c*Real.sqrt x*l x) at hx
    change _ < effectiveProbe m
    linarith only [hx,(abs_le.mp hb).1,hprice x m hxB hs h1]
  · obtain ⟨x,hx,hxM,hxB⟩ := (hhi.and_eventually late).exists
    obtain ⟨m,hm,hs,h1,hb⟩ := probe_at_real_cut M hxM
    refine ⟨m,hm,?_⟩
    change c*Real.sqrt x*l x < Chebyshev.psi x-x at hx
    change effectiveProbe m < _
    linarith only [hx,(abs_le.mp hb).2,hprice x m hxB hs h1]

#print axioms effective_endpoint_oscillations
#print axioms centeredWeilRow_de_la_vallee_poussin
#print axioms mixed_height_width_iff
#print axioms mixed_height_de_la_vallee_poussin
#print axioms mixed_height_bound
#print axioms completed_endpoint_de_la_vallee_poussin
#print axioms completed_endpoint_budget
#print axioms distance_to_completed_intersection

end GaloisForLFunctions.SignedArithmeticCorrespondences
