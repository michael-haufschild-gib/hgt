import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.DyadicTower

/-!
# Local supremum of the rejected Gibbs trace

Dilating a time interval and then halving the clock puts arbitrarily large
winding orders on block two inside the interval. The omitted geometric
tail gives the least upper bound, which no finite-order clock attains.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary Filter Set
open scoped Topology

/-- Halving preserves density at a given block while raising the minimum winding order. -/
theorem dense_large_order (H : ℕ+) (h : Dense {u : ℝ | ∃ e : u ∈ exceptional, block ⟨u,e⟩ = H}) (j : ℕ) :
    Dense {u : ℝ | ∃ e : u ∈ exceptional, block ⟨u,e⟩ = H ∧ 2^j ≤ windingOrder ⟨u,e⟩} := by
  induction j with
  | zero =>
    apply h.mono
    rintro u ⟨e,he⟩
    exact ⟨e,he,(order_nontrivial _).le⟩
  | succ j ih =>
    rw [Metric.dense_iff] at ih ⊢
    intro t ε hε
    obtain ⟨u,hd,e,hb,hm⟩ := ih (2*t) (2*ε) (by positivity)
    let v : ExceptionalTime := ⟨u,e⟩
    refine ⟨(halfClock v).val,?_,(halfClock v).property,(half_block v).trans hb,?_⟩
    · change dist (u/2) t < ε
      change dist u (2*t) < 2*ε at hd
      rw [Real.dist_eq,abs_lt] at hd ⊢
      constructor <;> linarith only [hd.1,hd.2]
    · rw [half_windingOrder,pow_succ']
      exact Nat.mul_le_mul_left 2 hm

/-- A single sequence in each ball realizes the block-two limit at all temperatures. -/
theorem local_block_two_limit (t : ℝ) (ε : {r : ℝ // 0 < r}) :
    ∃ v : ℕ → ExceptionalTime, (∀ j, dist (v j).val t < ε.val) ∧
      ∀ s : {z : ℂ // 0 < z.re}, Tendsto (fun j => response (v j) s.val) atTop
        (𝓝 (riemannZeta (2*s.val)*(2*heat s.val 2/(1-heat s.val 2)))) := by
  have pick (j : ℕ) : ∃ v : ExceptionalTime, dist v.val t < ε.val ∧ block v = 2 ∧ 2^j ≤ windingOrder v := by
    obtain ⟨u,hd,e,hb,hm⟩ := Metric.dense_iff.mp (dense_large_order 2 block_two_dense j) t ε.val ε.property
    exact ⟨⟨u,e⟩,hd,hb,hm⟩
  choose v hv hb hm using pick
  exact ⟨v,hv,fixed_block_limit v 2 hb (tendsto_atTop_mono hm
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℕ))))⟩

private def qReal (β : ℝ) (H : ℕ+) := Real.exp (-β*energy H)

private theorem heat_real (β : ℝ) (H : ℕ+) : heat (β:ℂ) H = (qReal β H : ℂ) := by
  simp only [heat,qReal,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]

private theorem q_lt {β : ℝ} (hβ : 0 < β) {H : ℕ+} (hH : 1 < H.val) : qReal β H < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact mul_neg_of_neg_of_pos (by linarith only [hβ]) (Real.log_pos (by exact_mod_cast hH))

private theorem radial_pos (β : {b : ℝ // 1/2 < b}) : 0 < (riemannZeta (2*(β.val:ℂ))).re := by
  have he : (2*(β.val:ℂ)) = ((2*β.val : ℝ):ℂ) := by push_cast; rfl
  rw [he]
  have hr := Complex.hasSum_re (heat_hasSum ⟨((2*β.val:ℝ):ℂ),by
    change 1 < 2*β.val; linarith only [β.property]⟩)
  have hw (n : ℕ+) : 0 < (heat ((2*β.val:ℝ):ℂ) n).re := by
    rw [heat_real,Complex.ofReal_re]
    exact Real.exp_pos _
  exact (hw 1).trans_le ((hr.summable.le_tsum 1 (fun n _ => (hw n).le)).trans_eq hr.tsum_eq)

/-- Largest limiting rejected trace at a real inverse temperature. -/
def envelope (β : {b : ℝ // 1/2 < b}) :=
  (riemannZeta (2*(β.val:ℂ))).re*(2*qReal β.val 2/(1-qReal β.val 2))

theorem envelope_eq (β : {b : ℝ // 1/2 < b}) :
    envelope β = 2*(riemannZeta (2*(β.val:ℂ))).re/((2:ℝ)^β.val-1) := by
  have hp : 0 < β.val := by linarith only [β.property]
  have hpow : 1 < (2:ℝ)^β.val := Real.one_lt_rpow (by norm_num) hp
  have hq : qReal β.val 2 = ((2:ℝ)^β.val)⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2:ℝ)),← Real.exp_neg]
    unfold qReal
    change Real.exp (-β.val*Real.log 2) = Real.exp (-(Real.log 2*β.val))
    congr 1; ring
  unfold envelope
  rw [hq]
  field_simp [(zero_lt_one.trans hpow).ne',sub_ne_zero.mpr hpow.ne']

private theorem re_times_weight (Z : ℂ) (q : ℝ) (m : ℕ) :
    (Z*(2*(q:ℂ)^m/(1-(q:ℂ)^m))).re = Z.re*(2*q^m/(1-q^m)) := by
  have he : (2*(q:ℂ)^m/(1-(q:ℂ)^m)) = ((2*q^m/(1-q^m):ℝ):ℂ) := by push_cast; rfl
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

private theorem re_times_sum (Z : ℂ) (q : ℝ) :
    (Z*(2*(q:ℂ)/(1-(q:ℂ)))).re = Z.re*(2*q/(1-q)) := by
  simpa only [pow_one] using re_times_weight Z q 1

private theorem real_tail (β : {b : ℝ // 1/2 < b}) (t : ExceptionalTime) :
    let q := qReal β.val (block t)
    let Z := (riemannZeta (2*(β.val:ℂ))).re
    Z*(2*q/(1-q))-(response t (β.val:ℂ)).re = Z*(2*q^(windingOrder t)/(1-q^(windingOrder t))) := by
  have hd := congrArg Complex.re (response_deficit t ⟨(β.val:ℂ),by change 0 < β.val; linarith only [β.property]⟩)
  simpa only [saturatedResponse,Complex.sub_re,heat_real,re_times_sum,re_times_weight] using hd

private theorem zero_correction (t : ℝ) (h : t ∉ exceptional) (s : ℂ) : correction t s = 0 := by
  letI : IsEmpty {x // rejected t x} := ⟨fun x => h ⟨x.val,x.property⟩⟩
  simp [correction,partition]

theorem loss_lt_envelope (β : {b : ℝ // 1/2 < b}) (t : ℝ) : (correction t (β.val:ℂ)).re < envelope β := by
  have hp : 0 < β.val := by linarith only [β.property]
  have h₂ : qReal β.val 2 < 1 := q_lt hp (by change 1 < 2; norm_num)
  have hq₂ : 0 < qReal β.val 2 := Real.exp_pos _
  by_cases ht : t ∈ exceptional
  · let v : ExceptionalTime := ⟨t,ht⟩
    rw [response_eq_heat_sum v ⟨_,β.property⟩]
    let q := qReal β.val (block v)
    have hq : 0 < q := Real.exp_pos _
    have hq₁ : q < 1 := q_lt hp (block_nontrivial v)
    have hm : windingOrder v ≠ 0 := by have := order_nontrivial v; omega
    have hqle : q ≤ qReal β.val 2 := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hp.le)
      exact Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ (block v).val from block_nontrivial v))
    have hf : 2*q/(1-q) ≤ 2*qReal β.val 2/(1-qReal β.val 2) := by
      apply (div_le_div_iff₀ (sub_pos.mpr hq₁) (sub_pos.mpr h₂)).mpr
      linarith only [hqle]
    have ht' := real_tail β v
    have htail : 0 < (riemannZeta (2*(β.val:ℂ))).re*(2*q^(windingOrder v)/(1-q^(windingOrder v))) :=
      mul_pos (radial_pos β) (div_pos (mul_pos two_pos (pow_pos hq _)) (sub_pos.mpr (pow_lt_one₀ hq.le hq₁ hm)))
    exact (sub_pos.mp (htail.trans_eq ht'.symm)).trans_le (mul_le_mul_of_nonneg_left hf (radial_pos β).le)
  · rw [zero_correction _ ht,Complex.zero_re]
    exact mul_pos (radial_pos β) (div_pos (mul_pos two_pos hq₂) (sub_pos.mpr h₂))

/-- A zero reading occurs in every ball, and all Gibbs readings are nonnegative. -/
theorem local_thermal_minimum (β : {b : ℝ // 1/2 < b}) (t : ℝ) (ε : {r : ℝ // 0 < r}) :
    IsLeast ((fun u => (correction u (β.val:ℂ)).re) '' Metric.ball t ε.val) 0 := by
  obtain ⟨u,hu,he⟩ := Metric.dense_iff.mp (exceptional_countable.dense_compl ℝ) t ε.val ε.property
  refine ⟨⟨u,hu,congrArg Complex.re (zero_correction u he (β.val:ℂ))⟩,?_⟩
  rintro _ ⟨v,_,rfl⟩
  have hs := ((sectorHeat_iff _ _).mp ((rejected_heat_iff v (β.val:ℂ)).mpr fun _ => β.property)).of_norm
  have hr := Complex.hasSum_re hs.hasSum
  change 0 ≤ (∑' i : {x // rejected v x}, wordHeat (β.val:ℂ) i.val).re
  rw [← hr.tsum_eq]
  apply tsum_nonneg
  intro i
  rw [wordHeat_total,heat_real,Complex.ofReal_re]
  exact (Real.exp_pos _).le

/-- The supremum of actual Gibbs readings on every open ball. -/
theorem local_thermal_supremum (β : {b : ℝ // 1/2 < b}) (t : ℝ) (ε : {r : ℝ // 0 < r}) :
    IsLUB ((fun u => (correction u (β.val:ℂ)).re) '' Metric.ball t ε.val)
      (2*(riemannZeta (2*(β.val:ℂ))).re/((2:ℝ)^β.val-1)) := by
  have hp : 0 < β.val := by linarith only [β.property]
  rw [← envelope_eq β]
  refine ⟨?_,?_⟩
  · rintro _ ⟨u,_,rfl⟩
    exact (loss_lt_envelope β u).le
  · intro B hB
    obtain ⟨v,hv,hL⟩ := local_block_two_limit t ε
    have hl := Complex.continuous_re.continuousAt.tendsto.comp (hL ⟨(β.val:ℂ),hp⟩)
    have hub (j : ℕ) : (response (v j) (β.val:ℂ)).re ≤ B := by
      rw [← response_eq_heat_sum (v j) ⟨_,β.property⟩]
      exact hB ⟨(v j).val,hv j,rfl⟩
    have hle := le_of_tendsto hl (Eventually.of_forall hub)
    simpa only [envelope,heat_real,re_times_sum] using hle

#print axioms dense_large_order
#print axioms local_block_two_limit
#print axioms loss_lt_envelope
#print axioms local_thermal_minimum
#print axioms local_thermal_supremum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
