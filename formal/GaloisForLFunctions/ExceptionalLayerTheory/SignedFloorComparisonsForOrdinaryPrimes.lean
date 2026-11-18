import GaloisForLFunctions.ExceptionalLayerTheory.TheOrdinaryPrimesSeparateSignedQuotientProfiles
import GaloisForLFunctions.ExceptionalLayerTheory.RationalGridJumpsOfRealFloorSums
import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Signed ordinary-prime comparisons of real floor sums

Summation over ordinary primes multiplies the Mellin transform by the
prime zeta function. Its logarithmic singularity at one detects every
nonzero floor-class difference, including balanced signed comparisons.
-/

noncomputable section
open MeasureTheory Finset Set Filter Topology Complex Asymptotics
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The sum of a profile over ordinary-prime quotients. For a profile
vanishing near zero only finitely many terms contribute at any positive cutoff. -/
def ordinaryPrimeRead (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' p : Nat.Primes, f (x/(p.1:ℝ))

private theorem prime_read_finite {f : ℝ → ℂ} {δ x : ℝ} (hδ : 0<δ) (hx : 0<x)
    (hz : ∀ t, 0<t → t<δ → f t=0) {N : ℕ} (hN : x/δ≤N) :
    ordinaryPrimeRead f x=∑ p ∈ Nat.primesLE N, f (x/(p:ℝ)) := by
  classical
  let S := (Nat.primesLE N).attach.map
    ⟨fun k => (⟨k.1,Nat.prime_of_mem_primesLE k.2⟩ : Nat.Primes),
      fun i j e => Subtype.ext (congrArg Subtype.val e)⟩
  have hmem (p : Nat.Primes) : p ∈ S ↔ p.1≤N := by
    constructor
    · intro hp
      obtain ⟨k,_,e⟩ := mem_map.mp hp
      exact (congrArg Subtype.val e) ▸ (Nat.mem_primesLE.mp k.2).1
    · intro hp
      let k : {n // n∈Nat.primesLE N} := ⟨p.1,Nat.mem_primesLE.mpr ⟨hp,p.2⟩⟩
      exact mem_map.mpr ⟨k,Finset.mem_attach _ _,Subtype.ext rfl⟩
  rw [ordinaryPrimeRead,tsum_eq_sum (s := S) (fun p hp => by
    have hlt : (N:ℝ)<p.1 := by exact_mod_cast lt_of_not_ge (fun hn => hp ((hmem p).mpr hn))
    have hpp : (0:ℝ)<p.1 := by exact_mod_cast p.2.pos
    exact hz _ (div_pos hx hpp) ((div_lt_iff₀ hpp).mpr
      (by linarith only [(div_lt_iff₀ hδ).mp (hN.trans_lt hlt)])))]
  simp only [S,sum_map,Function.Embedding.coeFn_mk]
  exact Finset.sum_attach _ _

private theorem local_of_bounded {f : ℝ → ℂ} (hm : Measurable f)
    (hb : ∀ T : ℝ, 0<T → ∃ B : ℝ, ∀ x : ℝ, 0<x → x<T → ‖f x‖≤B) :
    LocallyIntegrableOn f (Ioi 0) := by
  intro x hx
  have hx' : 0<x := hx
  obtain ⟨B,hB⟩ := hb (x+1) (by linarith only [hx'])
  refine ⟨Ioo 0 (x+1),mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx' (lt_add_one x)),?_⟩
  exact Measure.integrableOn_of_bounded (measure_Ioo_lt_top.ne) hm.aestronglyMeasurable
    ((ae_restrict_mem measurableSet_Ioo).mono fun t ht => hB t ht.1 ht.2)

private theorem read_local {f : ℝ → ℂ} (hm : Measurable f) {δ A : ℝ}
    (hδ : 0<δ) (hA : 0≤A) (hz : ∀ t, 0<t → t<δ → f t=0)
    (hb : ∀ t, 0<t → ‖f t‖≤A*t) : LocallyIntegrableOn (ordinaryPrimeRead f) (Ioi 0) := by
  apply local_of_bounded (Measurable.tsum (fun p : Nat.Primes => hm.comp (measurable_id.div_const _)))
  intro T hT
  obtain ⟨N,hN⟩ := exists_nat_ge (T/δ)
  refine ⟨(Nat.primesLE N).card*(A*T),fun x hx hxt => ?_⟩
  rw [prime_read_finite hδ hx hz ((div_le_div_of_nonneg_right hxt.le hδ.le).trans hN)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _ ∈ Nat.primesLE N, A*T := by
      refine sum_le_sum fun p hp => ?_
      have h1 : (1:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
      exact (hb _ (div_pos hx (zero_lt_one.trans_le h1))).trans (mul_le_mul_of_nonneg_left
        ((div_le_self hx.le h1).trans hxt.le) hA)
    _ = _ := by simp

private theorem near_zero_bound {f : ℝ → ℂ} {δ : ℝ} (hδ : 0<δ)
    (h : ∀ t, 0<t → t<δ → f t=0) (a : ℝ) : f =O[𝓝[>] 0] (fun x : ℝ => x^a) := by
  apply IsBigO.of_bound 0
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hδ)] with t ht ht'
  simp only [h t ht ht',norm_zero,zero_mul,le_refl]

private theorem mellin_diff_of_power {f : ℝ → ℂ} {b δ : ℝ} (hl : LocallyIntegrableOn f (Ioi 0))
    (hδ : 0<δ) (hz : ∀ t, 0<t → t<δ → f t=0) (h : f =O[atTop] (fun x : ℝ => x^b)) :
    DifferentiableOn ℂ (fun z : ℂ => mellin f (-z)) {z | b<z.re} := by
  intro z hzb
  have ht := mellin_differentiableAt_of_isBigO_rpow (s := -z) (a := -b)
    (b := -z.re-1) hl (by simpa only [neg_neg] using h) (by simpa using hzb)
    (near_zero_bound hδ hz ( -(-z.re-1))) (by simp only [neg_re]; linarith)
  exact (ht.comp z differentiableAt_neg).differentiableWithinAt

/-- The multiplicative change of variable at each prime also scales its
absolute Mellin integral, giving absolute convergence before interchange. -/
private theorem prime_read_mellin_real {f : ℝ → ℂ} {s : ℝ} (hs : 1<s)
    (hf : MellinConvergent f (-(s:ℂ))) :
    mellin (ordinaryPrimeRead f) (-(s:ℂ)) = (_root_.RHTower.primeZeta s:ℂ)*mellin f (-(s:ℂ)) := by
  let F (p : Nat.Primes) (t : ℝ) := (t:ℂ)^(-(s:ℂ)-1)*f (t/p.1)
  let G (t : ℝ) := ‖(t:ℂ)^(-(s:ℂ)-1)*f t‖
  have hpp (p : Nat.Primes) : (0:ℝ)<p.1 := by exact_mod_cast p.2.pos
  have hI (p : Nat.Primes) : IntegrableOn (F p) (Ioi 0) := by
    have h := (MellinConvergent.comp_mul_left (inv_pos.mpr (hpp p))).mpr hf
    simpa only [MellinConvergent,F,smul_eq_mul,div_eq_inv_mul] using h
  have hnorm (p : Nat.Primes) :
      (∫ t in Ioi (0:ℝ), ‖F p t‖)=(p.1:ℝ)^(-s)*(∫ t in Ioi (0:ℝ), G t) := by
    let d := (p.1:ℝ)
    have hd : 0<d := hpp p
    have he (t : ℝ) (ht : 0<t) : ‖F p t‖=d^(-s-1)*G (d⁻¹*t) := by
      have h' : 0<d⁻¹*t := mul_pos (inv_pos.mpr hd) ht
      simp only [F,G,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ht,
        Complex.norm_cpow_eq_rpow_re_of_pos h',sub_re,neg_re,ofReal_re,one_re,
        div_eq_inv_mul]
      rw [← mul_assoc,← Real.mul_rpow hd.le h'.le,mul_inv_cancel_left₀ hd.ne']
    rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,
      integral_comp_mul_left_Ioi G _ (inv_pos.mpr hd),mul_zero,inv_inv,smul_eq_mul,← mul_assoc]
    congr 1
    rw [Real.rpow_sub_one hd.ne',div_mul_cancel₀ _ hd.ne']
  have hsum := (_root_.RHTower.summable_primeZetaTerm hs).mul_right (∫ t in Ioi (0:ℝ),G t)
  have hswap := integral_tsum_of_summable_integral_norm hI (hsum.congr fun p => (hnorm p).symm)
  have hrow (p : Nat.Primes) : (∫ t in Ioi (0:ℝ), F p t) =
      (((p.1:ℝ)^(-s):ℝ):ℂ)*mellin f (-(s:ℂ)) := by
    change mellin (fun t : ℝ => f (t / p.1)) (-(s:ℂ))=_
    simp only [div_eq_inv_mul]
    rw [mellin_comp_mul_left f _ (inv_pos.mpr (hpp p)),neg_neg,smul_eq_mul,
      ← Complex.ofReal_cpow (inv_pos.mpr (hpp p)).le,Real.inv_rpow (hpp p).le,
      Real.rpow_neg (hpp p).le]
  rw [mellin]
  calc
    _ = ∫ t in Ioi (0:ℝ), ∑' p, F p t := by
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        simp only [ordinaryPrimeRead,F,smul_eq_mul,tsum_mul_left]
    _ = _ := by
      rw [← hswap]
      simp_rw [hrow]
      rw [tsum_mul_right,← Complex.ofReal_tsum]
      rfl

end GaloisForLFunctions.ExceptionalLayerTheory
