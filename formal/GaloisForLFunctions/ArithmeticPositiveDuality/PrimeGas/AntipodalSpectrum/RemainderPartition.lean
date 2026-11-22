import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RefinementTail

/-!
# Heat trace of the omitted occupations

Both orientations have an unrestricted radial coordinate and positive
multiples of the current winding order. A single radial row forces the
trace-class boundary; their full sum realizes the geometric deficit.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary

def windingWeight (t : ExceptionalTime) (j : ℕ) (s : ℂ) :=
  (heat s (block t))^(windingOrder (refined t j))

private theorem tail_heat (t : ExceptionalTime) (j : ℕ) (x : leastWords t) (s : ℂ) (p : TailIndex) :
    wordHeat s ((tailBasis t j x) p).val = (windingWeight t j s)^(p.2.1+1)*heat (2*s) p.2.2 := by
  change wordHeat s (ray _ _ _ _ _) = _
  rw [ray_heat,x.property.2,pow_mul]
  rfl

private theorem radial_norm (s : ℂ) (n : ℕ+) : ‖heat (2*s) n‖ = ‖heat s n‖^2 := by
  rw [two_mul,heat_add,norm_mul,pow_two]

theorem winding_contraction (t : ExceptionalTime) (j : ℕ) (s : {s : ℂ // 0 < s.re}) :
    ‖windingWeight t j s.val‖ < 1 := by
  rw [windingWeight,norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) (heat_contraction _ (block_nontrivial t) _ s.property)
    (Nat.ne_zero_of_lt (order_nontrivial _))

theorem remainder_heat_iff (t : ExceptionalTime) (j : ℕ) (s : ℂ) :
    HasSectorHeat (remainder t j) s ↔ 1/2 < s.re := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  let u : leastWords t := ⟨x,hx⟩
  let e := tailBasis t j u
  let q := windingWeight t j s
  have hw (p : TailIndex) : ‖wordHeat s (e p).val‖ = ‖q‖^(p.2.1+1)*‖heat s p.2.2‖^2 := by
    rw [tail_heat,norm_mul,norm_pow,radial_norm]
  rw [sectorHeat_iff]
  constructor
  · intro h
    have hs := (h.comp_injective (i := e) e.injective).congr hw
    have row : Summable (fun n : ℕ+ => ‖q‖^(0+1)*‖heat s n‖^2) := hs.comp_injective (i := fun n : ℕ+ => ((false,0,n) : TailIndex)) (fun _ _ he => congrArg (fun p : TailIndex => p.2.2) he)
    have hn : ‖q‖ ≠ 0 := (norm_pos_iff.mpr (pow_ne_zero _ (Complex.exp_ne_zero _)) : 0 < ‖q‖).ne'
    apply (summable_heat_sq_iff s).mp
    simpa only [Nat.zero_add,pow_one,← mul_assoc,inv_mul_cancel₀ hn,one_mul] using row.mul_left ‖q‖⁻¹
  · intro hs
    have hq : ‖q‖ < 1 := winding_contraction t j ⟨s,by linarith only [hs]⟩
    have hgeom : Summable (fun i : ℕ => ‖q‖^(i+1)) := by
      simpa only [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right ‖q‖
    have hrow := hgeom.mul_of_nonneg ((summable_heat_sq_iff s).mpr hs)
      (fun _ => pow_nonneg (norm_nonneg _) _) (fun _ => sq_nonneg _)
    have hsign : Summable (fun _ : Bool => (1:ℝ)) := Summable.of_finite
    have hall := hsign.mul_of_nonneg hrow
      (fun _ => zero_le_one) (fun p => mul_nonneg (pow_nonneg (norm_nonneg _) _) (sq_nonneg _))
    apply e.summable_iff.mp
    exact hall.congr fun p => (one_mul _).trans (hw p).symm

theorem remainder_partition (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // 1/2 < z.re}) :
    partition (remainder t j) s.val = riemannZeta (2*s.val)*(2*windingWeight t j s.val/(1-windingWeight t j s.val)) := by
  obtain ⟨x,hx⟩ := leastWords_nonempty t
  let u : leastWords t := ⟨x,hx⟩
  let e := tailBasis t j u
  let q := windingWeight t j s.val
  let W (p : ℕ × ℕ+) := q^(p.1+1)*heat (2*s.val) p.2
  have hs := ((sectorHeat_iff _ _).mp ((remainder_heat_iff t j s.val).mpr s.property)).of_norm
  have hs' : Summable (fun p : TailIndex => W p.2) :=
    (hs.comp_injective (i := e) e.injective).congr (tail_heat t j u s.val)
  have hrow : Summable W := hs'.comp_injective (i := fun p : ℕ × ℕ+ => (false,p)) (fun _ _ he => congrArg Prod.snd he)
  have hz : (∑' n : ℕ+, heat (2*s.val) n) = riemannZeta (2*s.val) := (heat_hasSum ⟨2*s.val,by rw [two_mul,Complex.add_re]; linarith only [s.property]⟩).tsum_eq
  have hq : ‖q‖ < 1 := winding_contraction t j ⟨s.val,by linarith only [s.property]⟩
  have hsum : ∑' p, W p = (q*(1-q)⁻¹)*riemannZeta (2*s.val) := by
    rw [hrow.tsum_prod]
    simp only [W,tsum_mul_left,hz,tsum_mul_right,pow_succ',tsum_geometric_of_norm_lt_one hq]
  calc
    partition (remainder t j) s.val = ∑' p, wordHeat s.val (e p).val := (e.tsum_eq _).symm
    _ = ∑' p : TailIndex, W p.2 := tsum_congr (tail_heat t j u s.val)
    _ = ∑' _ : Bool, ∑' p, W p := hs'.tsum_prod
    _ = _ := by rw [tsum_bool,hsum]; change _ = riemannZeta _*(2*q/(1-q)); ring

theorem remainder_operator_trace (t : ExceptionalTime) (j : ℕ) (s : {z : ℂ // AbsoluteHeat (remainder t j) z}) :
    ContinuousLinearMap.opTrace (sectorHeat (remainder t j) s) =
      saturatedResponse t s.val - response (refined t j) s.val := by
  have hβ := (remainder_heat_iff t j _).mp ((sectorHeat_iff _ _).mpr s.property)
  rw [operator_trace,remainder_partition t j ⟨s.val,hβ⟩,refined_deficit t ⟨s.val,by linarith only [hβ]⟩]
  simp only [windingWeight,(refined_parameters t j).2.2]

#print axioms remainder_heat_iff
#print axioms remainder_partition
#print axioms remainder_operator_trace

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
