import GaloisForLFunctions.Hurwitz.ShiftedPowerTailAsymptotic

/-!
# Real power tails with asymptotically constant coefficients

The real-mesh count gives an explicit error of one mesh cell at every
shift. Bounded perturbations with a limiting coefficient change the
leading constant by exactly that coefficient.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace GaloisForLFunctions.HurwitzPowerTails

/-- Positive-shift tail at any real order above the summability threshold. -/
def powerTail (p x : ℝ) : ℝ := ∑' n : ℕ, ((n:ℝ)+x)^(-(p+1))

/-- A positive real shift has a uniform one-cell remainder. -/
theorem scaled_power_tail_bounds {p x : ℝ} (hp : 0<p) (hx : 0<x) :
    1/p ≤ x^p*powerTail p x ∧ x^p*powerTail p x ≤ 1/p+1/x := by
  let f := fun t : ℝ => (t+x)^(-(p+1))
  have hm := measurePreserving_add_right (volume : Measure ℝ) x
  have hset : (fun t : ℝ => t+x) ⁻¹' Ioi x = Ioi 0 := by ext t; simp
  have hi : IntegrableOn f (Ioi 0) := by
    rw [←hset]
    exact (hm.integrableOn_comp_preimage (measurableEmbedding_addRight x)).mpr
      (integrableOn_Ioi_rpow_of_lt (by linarith only [hp]) hx)
  have hval : ∫ t in Ioi 0, f t = x^(-p)/p := by
    have tr := hm.setIntegral_preimage_emb (measurableEmbedding_addRight x)
      (fun t : ℝ => t^(-(p+1))) (Ioi x)
    rw [hset] at tr
    rw [tr,integral_Ioi_rpow_of_lt (by linarith only [hp]) hx,
      show -(p+1)+1 = -p by ring,neg_div_neg_eq]
  have hanti : AntitoneOn f (Ici 0) := fun a ha b _ hab =>
    Real.rpow_le_rpow_of_nonpos (by change 0 ≤ a at ha; linarith) (add_le_add_right hab _) (by linarith)
  have hnn : ∀ t ∈ Ici (0:ℝ), 0 ≤ f t := fun t ht => Real.rpow_nonneg (add_nonneg ht hx.le) _
  have h := HTGeometry.realMesh_antitone_Ioi_bounds hanti hnn hi (i:=1) zero_lt_one
  simp only [one_div_one,one_mul,div_one,hval,f,zero_add] at h
  have lo := mul_le_mul_of_nonneg_left h.1 (Real.rpow_nonneg hx.le p)
  have hi' := mul_le_mul_of_nonneg_left h.2 (Real.rpow_nonneg hx.le p)
  have pair : x^p*x^(-p) = 1 := by rw [←Real.rpow_add hx,add_neg_cancel,Real.rpow_zero]
  have edge : x^p*x^(-(p+1)) = 1/x := by rw [←Real.rpow_add hx,show p+ -(p+1) = -1 by ring,Real.rpow_neg_one,one_div]
  rw [←mul_div_assoc,pair] at lo
  rw [mul_add,←mul_div_assoc,pair,edge] at hi'
  exact ⟨lo,hi'⟩

/-- Exact positive-real order extension of the shifted Hurwitz tail limit. -/
theorem tendsto_scaled_power_tail {p : ℝ} (hp : 0<p) :
    Tendsto (fun x : ℝ => x^p*powerTail p x) atTop (𝓝 (1/p)) := by
  have h := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop)
  have hu := h.const_add (1/p)
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact (eventually_gt_atTop (0:ℝ)).mono fun x hx => (scaled_power_tail_bounds hp hx).1
  · exact (eventually_gt_atTop (0:ℝ)).mono fun x hx => (scaled_power_tail_bounds hp hx).2

private abbrev weight (p : ℝ) (n : ℕ) := (n:ℝ)^(-(p+1))

/-- Even signed coefficients tending to c give the tail c/(p N^p)
at every real p>0. The absolute convergence is part of the conclusion. -/
theorem perturbed_power_tail {a : ℕ → ℝ} {c p : ℝ} (hp : 0<p)
    (ha : Tendsto a atTop (𝓝 c)) :
    Summable (fun n => a n*weight p n) ∧
    Tendsto (fun N : ℕ => (N:ℝ)^p*∑' k : ℕ, a (k+N)*weight p (k+N)) atTop (𝓝 (c/p)) := by
  have sw : Summable (weight p) := Real.summable_nat_rpow.mpr (by linarith only [hp])
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp ha 1 zero_lt_one
  have sa : Summable (fun n => a n*weight p n) := by
    apply (sw.mul_left (|c|+1)).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop K] with n hn
    have h := hK n hn
    rw [Real.dist_eq] at h
    have bnd := abs_add_le (a n-c) c
    rw [sub_add_cancel] at bnd
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right (by linarith only [h,bnd]) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨sa,?_⟩
  let H := fun N : ℕ => (N:ℝ)^p*(∑' k : ℕ, weight p (k+N))
  have base : Tendsto H atTop (𝓝 (1/p)) := by
    simpa only [H,Function.comp_apply,weight,Nat.cast_add,powerTail] using
      (tendsto_scaled_power_tail hp).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have diff : Tendsto (fun N : ℕ => (N:ℝ)^p*(∑' k : ℕ, a (k+N)*weight p (k+N))-c*H N)
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε ep
    let δ := ε/(2*(1+1/p))
    have hden : 0 < 2*(1+1/p) := by positivity
    obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp ha δ (div_pos ep hden)
    refine ⟨max 1 M,fun N hn => ?_⟩
    have hN := (le_max_left 1 M).trans hn
    have ns := (summable_nat_add_iff N).mpr sw
    have as' := (summable_nat_add_iff N).mpr sa
    let w := fun k => weight p (k+N)
    have nn (k : ℕ) : 0 ≤ w k := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have he (k : ℕ) : |a (k+N)-c| ≤ δ := by
      simpa only [Real.dist_eq] using (hM (k+N) (by omega)).le
    have bounds (k : ℕ) := abs_le.mp (he k)
    have diffSum := as'.sub (ns.mul_left c)
    have lo := (ns.mul_left (-δ)).tsum_le_tsum
      (fun k => show -δ*w k ≤ a (k+N)*w k-c*w k by
        rw [←sub_mul]; exact mul_le_mul_of_nonneg_right (bounds k).1 (nn k)) diffSum
    have hi := diffSum.tsum_le_tsum
      (fun k => show a (k+N)*w k-c*w k ≤ δ*w k by
        rw [←sub_mul]; exact mul_le_mul_of_nonneg_right (bounds k).2 (nn k)) (ns.mul_left δ)
    rw [tsum_mul_left,as'.tsum_sub (ns.mul_left c),tsum_mul_left] at lo
    rw [as'.tsum_sub (ns.mul_left c),tsum_mul_left,tsum_mul_left] at hi
    have scale := Real.rpow_nonneg (Nat.cast_nonneg N) p
    have ht := (scaled_power_tail_bounds hp (Nat.cast_pos.mpr hN : 0<(N:ℝ))).2
    have hN1 : 1/(N:ℝ) ≤ 1 := (div_le_one (Nat.cast_pos.mpr hN)).mpr (Nat.one_le_cast.mpr hN)
    have hH : H N ≤ 1+1/p := by
      simp only [H,weight,Nat.cast_add,powerTail] at ht ⊢
      linarith only [ht,hN1]
    have hδ : 0 < δ := div_pos ep hden
    have hε : δ*(1+1/p) = ε/2 := by dsimp only [δ]; field_simp
    have bound := mul_le_mul_of_nonneg_left hH hδ.le
    rw [hε] at bound
    have hm := mul_le_mul_of_nonneg_left lo scale
    have hp' := mul_le_mul_of_nonneg_left hi scale
    rw [Real.dist_eq,sub_zero,abs_lt]
    dsimp only [H] at bound ⊢
    constructor <;> linarith only [hm,hp',bound,ep]
  have lim := diff.add (base.const_mul c)
  rw [zero_add,one_div,←div_eq_mul_inv] at lim
  exact lim.congr fun N => sub_add_cancel _ _

#print axioms scaled_power_tail_bounds
#print axioms perturbed_power_tail
end GaloisForLFunctions.HurwitzPowerTails
