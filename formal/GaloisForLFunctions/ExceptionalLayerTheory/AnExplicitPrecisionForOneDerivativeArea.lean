import GaloisForLFunctions.ExceptionalLayerTheory.OneLogarithmicDerivativeOrderReadsTheXiHistogram
import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation
import GaloisForLFunctions.HTGeometry.RadicalTowerDegree

/-!
# Precision for a single derivative-area reading

A nonzero integer combination of positive p-th roots is an algebraic
integer in a field of degree at most p^W for W radicands. Its conjugates
are bounded by the unsigned weighted sum. The norm gives a lower bound
on the separation of competing predictions, hence an explicit absolute
error tolerance for one area reading.
-/

noncomputable section
open Complex Filter Topology NumberField RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def radicalWeight (p m : ℕ) := (m:ℝ)^((p:ℝ)⁻¹)

/-- Separation for all positive root degrees p, including radicands
with multiplicative dependencies. Only distinct sums are separated. -/
theorem quantitative_radical_sum {W p : ℕ} (hp : 0<p) (m : Fin W → ℕ) (c : Fin W → ℤ)
    (hn : (∑ i, (c i:ℝ)*(m i:ℝ)^((p:ℝ)⁻¹))≠0) :
    ((1+∑ i, |(c i:ℝ)| * (m i:ℝ)^((p:ℝ)⁻¹))^(p^W-1))⁻¹ ≤
      |∑ i, (c i:ℝ)*(m i:ℝ)^((p:ℝ)⁻¹)| := by
  classical
  let x (i : Fin W) : ℂ := (radicalWeight p (m i):ℂ)
  have hx (i : Fin W) : (x i)^p=(m i:ℂ) := by
    exact_mod_cast Real.rpow_inv_natCast_pow (Nat.cast_nonneg (m i) : (0:ℝ) ≤ m i) hp.ne'
  let K := IntermediateField.adjoin ℚ (Set.range x)
  letI : Finite (Set.range x) := Set.finite_range x
  letI : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨i,rfl⟩
    apply IsIntegral.of_pow hp
    rw [hx]
    simpa only [map_natCast] using (isIntegral_algebraMap (R:=ℚ) (A:=ℂ) (x:=(m i:ℚ))))
  letI : NumberField K := ⟨⟩
  have hdeg : Module.finrank ℚ K≤p^W := by
    have h := HTGeometry.finrank_adjoin_image_le_prod (F:=ℚ) x (fun _ => p) (fun _ => hp)
      (fun i => ⟨(m i:ℚ),by rw [hx,map_natCast]⟩) Finset.univ
    simpa only [Finset.coe_univ,Set.image_univ,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h
  let b (i : Fin W) : K := ⟨x i,IntermediateField.subset_adjoin _ _ (Set.mem_range_self i)⟩
  have hb (i : Fin W) : b i^p=(m i:K) := Subtype.ext (hx i)
  have hint (i : Fin W) : IsIntegral ℤ (b i) := by
    apply IsIntegral.of_pow hp
    rw [hb]
    exact isIntegral_natCast (m i)
  let v : K := ∑ i, (c i:K)*b i
  let σ₀ : K →+* ℂ := K.val.toRingHom
  have hreal : σ₀ v = ((∑ i, (c i:ℝ)*radicalWeight p (m i):ℝ):ℂ) := by
    simp only [v,map_sum,map_mul,map_intCast,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast]
    rfl
  have hv : v≠0 := fun he => hn (Complex.ofReal_injective (by rw [←hreal,he,map_zero,Complex.ofReal_zero]))
  let β : 𝓞 K := ⟨v,IsIntegral.sum _ fun i _ => (isIntegral_intCast (c i)).mul (hint i)⟩
  let B := 1+∑ i, |(c i:ℝ)| * radicalWeight p (m i)
  have hB : 1≤B := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hc (σ : K →+* ℂ) (i : Fin W) : ‖σ (b i)‖=radicalWeight p (m i) := by
    apply (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hp.ne').mp
    rw [←norm_pow,←map_pow,hb,map_natCast,Complex.norm_natCast]
    exact (Real.rpow_inv_natCast_pow (Nat.cast_nonneg (m i)) hp.ne').symm
  have hσ (σ : K →+* ℂ) : ‖σ v‖ ≤ B := by
    simp only [v,map_sum,map_mul,map_intCast]
    have hz := norm_sum_le Finset.univ (fun i => (c i:ℂ)*σ (b i))
    simp only [norm_mul,Complex.norm_intCast,hc,Int.cast_abs] at hz
    exact hz.trans (le_add_of_nonneg_left zero_le_one)
  have H := HTGeometry.inv_pow_le_norm_embedding β (fun h => hv (congrArg Subtype.val h)) σ₀
    (zero_lt_one.trans_le hB) (fun σ _ => hσ σ)
  change _ ≤ ‖σ₀ v‖ at H
  rw [NumberField.Embeddings.card,hreal,Complex.norm_real,Real.norm_eq_abs] at H
  exact (inv_anti₀ (pow_pos (zero_lt_one.trans_le hB) _) (pow_le_pow_right₀ hB
    (Nat.sub_le_sub_right hdeg 1))).trans H

/-- Guaranteed gap between different bounded integer predictions. -/
def derivativeAreaGap (W p : ℕ) : ℝ := ((1+2*(W:ℝ)^2)^(p^W-1))⁻¹

theorem prime_area_gap {W p : ℕ} (hp : p.Prime) (hW : W<2^p)
    (a b : BoundedOrderCounts W) (hab : a≠b) :
    derivativeAreaGap W p ≤ |boundedOrderMoment (2*p-1) a-boundedOrderMoment (2*p-1) b| := by
  let m (i : Fin W) := i.val+1
  let c (i : Fin W) : ℤ := ((a i).val:ℤ)-(b i).val
  have hn : boundedOrderMoment (2*p-1) a≠boundedOrderMoment (2*p-1) b := by
    intro h
    have hh : (fun i => ((a i).val:ℚ))=(fun i => ((b i).val:ℚ)) :=
      prime_derivative_area_injective hp hW (by simpa only [Rat.cast_natCast] using h)
    exact hab (funext fun k => Fin.ext (by exact_mod_cast congrFun hh k))
  have he : boundedOrderMoment (2*p-1) a-boundedOrderMoment (2*p-1) b =
      ∑ i, (c i:ℝ)*(m i:ℝ)^((p:ℝ)⁻¹) := by
    simp only [boundedOrderMoment,divisorAreaMoment,←Finset.sum_sub_distrib,←mul_sub,
      prime_order_weight hp.pos,c,m,Int.cast_sub,Int.cast_natCast,mul_comm]
  have hsum : 1+∑ i, |(c i:ℝ)| * (m i:ℝ)^((p:ℝ)⁻¹)≤1+2*(W:ℝ)^2 := by
    refine add_le_add le_rfl ?_
    have hbound (i : Fin W) : |(c i:ℝ)| * (m i:ℝ)^((p:ℝ)⁻¹) ≤ (W:ℝ)*2 := by
      have h₁ : |(c i:ℝ)|≤W := by
        have ha : ((a i).val:ℝ)≤W := by exact_mod_cast Nat.le_of_lt_succ (a i).isLt
        have hb : ((b i).val:ℝ)≤W := by exact_mod_cast Nat.le_of_lt_succ (b i).isLt
        simp only [c,Int.cast_sub,Int.cast_natCast,abs_le]
        constructor
        · linarith only [hb,(Nat.cast_nonneg (a i).val : (0:ℝ)≤(a i).val)]
        · linarith only [ha,(Nat.cast_nonneg (b i).val : (0:ℝ)≤(b i).val)]
      have h₂ : (m i:ℝ)^((p:ℝ)⁻¹)≤2 := by
        have h := Real.rpow_le_rpow (Nat.cast_nonneg (m i) : (0:ℝ) ≤ m i)
          (by exact_mod_cast ((Nat.succ_le_of_lt i.isLt).trans hW.le) : (m i:ℝ)≤((2^p:ℕ):ℝ))
          (inv_nonneg.mpr (Nat.cast_nonneg p))
        simpa only [Nat.cast_pow,Nat.cast_ofNat,Real.pow_rpow_inv_natCast (by norm_num : (0:ℝ)≤2)
          hp.ne_zero] using h
      exact mul_le_mul h₁ h₂ (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
    calc _ ≤ ∑ _i : Fin W, (W:ℝ)*2 := Finset.sum_le_sum fun i _ => hbound i
         _ = 2*(W:ℝ)^2 := by simp; ring
  have hnonzero := sub_ne_zero.mpr hn
  rw [he] at hnonzero ⊢
  exact (inv_anti₀ (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hsum _)).trans
    (quantitative_radical_sum hp.pos m c hnonzero)

/-- An absolute error below half the explicit gap certifies the unique
nearest histogram even for an adversarial perturbation of the reading. -/
theorem prime_area_error_tolerance {W p : ℕ} (hp : p.Prime) (hW : W<2^p)
    (a : BoundedOrderCounts W) (x : ℝ)
    (hx : |x-boundedOrderMoment (2*p-1) a|<derivativeAreaGap W p/2) (b : BoundedOrderCounts W) :
    (∀ e, |x-boundedOrderMoment (2*p-1) b|≤|x-boundedOrderMoment (2*p-1) e|) ↔ b=a := by
  let v := boundedOrderMoment (W:=W) (2*p-1)
  have hs (e : BoundedOrderCounts W) (he : e≠a) : |x-v a| < |x-v e| := by
    have ht := abs_sub_le (v a) x (v e)
    rw [abs_sub_comm (v a) x] at ht
    have hg := prime_area_gap hp hW a e he.symm
    change derivativeAreaGap W p≤|v a-v e| at hg
    change |x-v a|<derivativeAreaGap W p/2 at hx
    linarith only [ht,hg,hx]
  constructor
  · intro hm
    by_contra he
    exact (hs b he).not_ge (hm a)
  · rintro rfl e
    by_cases he : e=a
    · rw [he]
    · exact (hs e he).le

#print axioms quantitative_radical_sum
#print axioms prime_area_gap
#print axioms prime_area_error_tolerance
end GaloisForLFunctions.ExceptionalLayerTheory
