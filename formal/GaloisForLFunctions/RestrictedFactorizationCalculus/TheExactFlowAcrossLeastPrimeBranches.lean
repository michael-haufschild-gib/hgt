import GaloisForLFunctions.RestrictedFactorizationCalculus.SaturationAtTheFourthRoot
import GaloisForLFunctions.RHTower.MobiusPrimeSemiprimeCellMatching

/-!
# Paying the exact imbalance of the fourth-root least-prime branches

Each triple contracts inside its own branch. The remaining semiprimes
split their larger factor into a product with least prime 2, 3 or 5.
The original least prime becomes the middle prime of that product, so
different rows have disjoint images. The number of external targets
is exactly the signed mass of the region.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem small_prime_capacity : ∀ᶠ T : ℝ in atTop,
    (windowPrimes T (2*T)).card ≤ (semiprimeTargets T (2*T)).card := by
  obtain ⟨H,_,hu⟩ := exists_card_windowPrimes_le 0 (ε := 1/100) (by norm_num)
  obtain ⟨L,_,hl⟩ := exists_card_windowPrimes_div_ge 0 (ε := 1/100) (by norm_num)
  filter_upwards [eventually_ge_atTop (30:ℝ),eventually_ge_atTop H,eventually_ge_atTop L] with T ht hH hL
  have hle : T ≤ 2*T := by linarith only [ht]
  have hgap : T/Real.log T^(0:ℝ) ≤ 2*T-T := by rw [Real.rpow_zero,div_one]; linarith
  have h := hu T hH T (2*T) le_rfl hle le_rfl hgap
  exact_mod_cast h.trans (semiprimeTargets_card_ge ht hle (Real.log_pos (by linarith only [ht]))
    (fun q hq => hl T hL q (by exact_mod_cast (small_cofactor_cases hq).2.1)
      (by exact_mod_cast (small_cofactor_cases hq).2.2) T (2*T) le_rfl hle le_rfl hgap))

private theorem assemble_exports {S V H : Finset ℕ} (hV : V ⊆ S)
    (A : OppositeParityMatching GlobalDyadicOneTwoRel H) (hA : A.sources ⊆ posParity V)
    (hD : A.targets=negParity V) (f : ℕ → ℕ) (hinj : Set.InjOn f (posParity V))
    (hf : ∀ n ∈ posParity V,f n ∈ negParity S ∧ f n ∉ V ∧
      (f n).minFac ∈ ({2,3,5}:Finset ℕ) ∧ GlobalDyadicOneTwoRel n (f n)) :
    ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel S, M.sources=posParity V ∧
      negParity V ⊆ M.targets ∧ (∀ n ∈ M.targets \ V,n.minFac ∈ ({2,3,5}:Finset ℕ)) ∧
      ((M.targets \ V).card:ℤ)=∑ n ∈ V,μ n := by
  let g (n : ℕ) := if n ∈ A.sources then A.partner n else f n
  have ha (n : ℕ) (hn : n ∈ A.sources) : A.partner n ∈ negParity V :=
    hD ▸ mem_image_of_mem A.partner hn
  have hv (n : ℕ) (hn : n ∈ A.sources) : A.partner n ∈ V := (mem_filter.mp (ha n hn)).1
  let M : OppositeParityMatching GlobalDyadicOneTwoRel S := {
    sources := posParity V
    partner := g
    sources_subset := fun n hn => mem_filter.mpr ⟨hV (mem_filter.mp hn).1,(mem_filter.mp hn).2⟩
    injOn := by
      intro n hn m hm he
      dsimp only [g] at he
      split_ifs at he with h h'
      · exact A.injOn h h' he
      · exact ((hf m hm).2.1 (he ▸ hv n h)).elim
      · exact ((hf n hn).2.1 (he ▸ hv m h')).elim
      · exact hinj hn hm he
    partner_mem := by
      intro n hn
      change g n ∈ negParity S
      dsimp only [g]
      split_ifs with h
      · exact mem_filter.mpr ⟨hV (hv n h),(mem_filter.mp (ha n h)).2⟩
      · exact (hf n hn).1
    adj := by
      intro n hn
      change GlobalDyadicOneTwoRel n (g n)
      dsimp only [g]
      split_ifs with h
      · exact A.adj _ h
      · exact (hf n hn).2.2.2 }
  have hneg : negParity V ⊆ M.targets := by
    intro n hn
    rw [←hD] at hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    exact mem_image.mpr ⟨m,hA hm,if_pos hm⟩
  have he : M.targets ∩ V=negParity V := by
    ext n
    exact ⟨fun h => mem_filter.mpr ⟨(mem_inter.mp h).2,(mem_filter.mp (M.targets_subset (mem_inter.mp h).1)).2⟩,
      fun h => mem_inter.mpr ⟨hneg h,(mem_filter.mp h).1⟩⟩
  refine ⟨M,rfl,hneg,?_,?_⟩
  · intro n hn
    obtain ⟨ht,hout⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨m,hm,rfl⟩ := mem_image.mp ht
    change (g m).minFac ∈ _
    by_cases ha : m ∈ A.sources
    · exact (hout (show g m ∈ V by dsimp only [g]; rw [if_pos ha]; exact hv m ha)).elim
    · dsimp only [g]
      rw [if_neg ha]
      exact (hf m hm).2.2.1
  · have hcount := card_inter_add_card_sdiff M.targets V
    rw [he,M.card_targets] at hcount
    change (negParity V).card + _ = (posParity V).card at hcount
    rw [sum_moebius_eq_card_pos_sub_neg]
    omega

private def splitLarger (X n : ℕ) : ℕ :=
  let p := n.minFac
  let T := (X:ℝ)/p
  p*rankedSlot (windowPrimes T (2*T)) (semiprimeTargets T (2*T)) (n/p)

private theorem split_in_row {X n : ℕ} (hn : n ∈ Ioc X (2*X)) (hsq : Squarefree n)
    (hm : μ n=1) (hp : n.minFac.Prime) (hz : (n/n.minFac).Prime) (hbig : 5<n.minFac)
    (hscale : 5*n.minFac^2 ≤ X) (hc : let T := (X:ℝ)/n.minFac
      (windowPrimes T (2*T)).card ≤ (semiprimeTargets T (2*T)).card)
    (h30 : 30 ≤ (X:ℝ)/n.minFac) :
    let N := splitLarger X n
    let p := n.minFac
    let T := (X:ℝ)/p
    N ∈ negParity (Ioc X (2*X)) ∧ N.minFac ∈ ({2,3,5}:Finset ℕ) ∧
      (N/N.minFac).minFac=p ∧ GlobalDyadicOneTwoRel n N ∧ n/p ∈ windowPrimes T (2*T) := by
  let p := n.minFac
  let z := n/p
  let T := (X:ℝ)/p
  let W := rankedSlot (windowPrimes T (2*T)) (semiprimeTargets T (2*T)) z
  let N := splitLarger X n
  have hprod : z*p=n := Nat.div_mul_cancel (Nat.minFac_dvd n)
  have hzr : (z:ℝ)*p=n := by exact_mod_cast hprod
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hT0 : 0 ≤ T := div_nonneg (Nat.cast_nonneg _) hp0.le
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hn
  have hxn : (X:ℝ)<n := by exact_mod_cast hlo
  have hnx : (n:ℝ) ≤ 2*X := by exact_mod_cast hhi
  have hzwin : z ∈ windowPrimes T (2*T) := by
    refine (mem_windowPrimes hT0 (by positivity)).2 ⟨hz,(div_lt_iff₀ hp0).2 (hzr ▸ hxn),?_⟩
    change (z:ℝ) ≤ 2*((X:ℝ)/p)
    rw [←mul_div_assoc,le_div_iff₀ hp0,hzr]; exact hnx
  have hwin : W ∈ semiprimeTargets T (2*T) := rankedSlot_mem hc hzwin
  obtain ⟨a,b,ha,hb,_,hW,hl,hu⟩ := mem_semiprimeTargets h30 (by linarith only [hT0]) hwin
  have has : a ∈ ({2,3,5}:Finset ℕ) := by simpa only [mem_insert,mem_singleton] using ha
  obtain ⟨hap,_,ha5⟩ := small_cofactor_cases has
  have hNW : N=W*p := Nat.mul_comm ..
  have hrlo := (div_lt_iff₀ hp0).1 hl
  have hupper : (W:ℝ) ≤ 2*(X:ℝ)/p := by simpa only [mul_div_assoc] using hu
  have hrhi := (le_div_iff₀ hp0).1 hupper
  have hlow : X<W*p := by exact_mod_cast hrlo
  have hhigh : W*p ≤ 2*X := by exact_mod_cast hrhi
  have hpb : p<b := by
    by_contra! h
    have hab := Nat.mul_le_mul ha5 h
    rw [←hW] at hab
    have hh := Nat.mul_le_mul_right p hab
    have hh' : 5*p*p=5*p^2 := by ring
    exact hlow.not_ge ((hh.trans_eq hh').trans hscale)
  have hap' : a<p := ha5.trans_lt hbig
  have hrp := append_smallest hb.one_lt hp (by rwa [hb.minFac_eq])
  have hbp : 1<b*p := hb.one_lt.trans_le (Nat.le_mul_of_pos_right b hp.pos)
  have hsmall := append_smallest hbp hap (by rwa [hrp.1])
  have form : N=(b*p)*a := by rw [hNW,hW]; ring
  have hsN : Squarefree N := by
    rw [form]; exact Nat.squarefree_mul_iff.mpr ⟨hsmall.2,
      Nat.squarefree_mul_iff.mpr ⟨hrp.2,Irreducible.squarefree hb,Irreducible.squarefree hp⟩,Irreducible.squarefree hap⟩
  have hmu : μ N = -1 := by
    rw [form,isMultiplicative_moebius.map_mul_of_coprime hsmall.2,
      isMultiplicative_moebius.map_mul_of_coprime hrp.2,moebius_apply_prime hb,
      moebius_apply_prime hp,moebius_apply_prime hap]; decide
  have hmin : N.minFac=a := form ▸ hsmall.1
  refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨hNW ▸ hlow,hNW ▸ hhigh⟩,hmu⟩,
    hmin ▸ has,?_,?_,hzwin⟩
  · rw [hmin,form,Nat.mul_div_cancel _ hap.pos,hrp.1]
  · exact ⟨hsq,hsN,by rw [hm,hmu]; decide,p,z,a,b,hz,hap,hb,hap'.trans hpb,
      Or.inl ⟨hprod.symm.trans (Nat.mul_comm ..),by change p*W=p*(a*b); rw [hW]⟩⟩

/-- All vertices of the fourth-root least-prime region can be covered.
Exactly its signed excess exits the region, and every external target has
least prime 2, 3 or 5. Each source and each target is used only once. -/
theorem eventually_exact_least_prime_exports :
    ∀ᶠ X : ℕ in atTop, ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
      M.sources=posParity (fourthRootBranches X) ∧ negParity (fourthRootBranches X) ⊆ M.targets ∧
      (∀ n ∈ M.targets \ fourthRootBranches X,n.minFac ∈ ({2,3,5}:Finset ℕ)) ∧
      ((M.targets \ fourthRootBranches X).card:ℤ) = ∑ n ∈ fourthRootBranches X,μ n := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp small_prime_capacity
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^(1/16:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_fourth_root_child_capacity,eventually_ge_atTop 1,
    hlim.eventually_ge_atTop (max 30 H)] with X hchild hX ht
  let t := (X:ℝ)^(1/16:ℝ)
  let y := ⌊2*t^4⌋₊
  let V := fourthRootBranches X
  let W := windowPrimes (2*t^4) (t^5)
  let S := roughTails X (2*X) y
  have ht30 : 30 ≤ t := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ t := by linarith only [ht30]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hX0 : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
  have h16 : t^16=X := by dsimp [t]; rw [←Real.rpow_natCast,←Real.rpow_mul hX0]; norm_num
  have hpows {a b : ℕ} (h : a ≤ b) : t^a ≤ t^b := pow_le_pow_right₀ ht1 h
  have ht4 : t ≤ t^4 := by simpa only [pow_one] using hpows (by decide : 1 ≤ 4)
  have hfour : 2*X ≤ y^4 := by
    have hf := Nat.lt_floor_add_one (2*t^4)
    have hy : (3/2:ℝ)*t^4 ≤ y := by dsimp only [y]; linarith only [hf,ht30,ht4]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (3/2:ℝ)*t^4) hy 4
    have hXX : 2*(X:ℝ) ≤ (y:ℝ)^4 := by nlinarith only [hh,h16,hX0]
    exact_mod_cast hXX
  have hV {n : ℕ} (hn : n ∈ V) : n ∈ S ∧ n.minFac ∈ W := by
    obtain ⟨hr,hp⟩ := mem_filter.mp hn
    obtain ⟨h1,hl,hu,hs,_⟩ := mem_roughTails.mp hr
    have hlow := ((mem_windowPrimes (by positivity) (by positivity)).1 hp).2.1
    exact ⟨mem_roughTails.mpr ⟨h1,hl,hu,hs,(Nat.floor_lt (by positivity)).2 hlow⟩,hp⟩
  have fromS {n : ℕ} (hn : n ∈ S) (hp : n.minFac ∈ W) : n ∈ V := by
    obtain ⟨h1,hl,hu,hs,hy⟩ := mem_roughTails.mp hn
    exact mem_filter.mpr ⟨mem_roughTails.mpr ⟨h1,hl,hu,hs,Nat.zero_le y |>.trans_lt hy⟩,hp⟩
  have hVI : V ⊆ Ioc X (2*X) := fun n hn =>
    mem_Ioc.mpr ⟨(mem_roughTails.mp (hV hn).1).2.1,(mem_roughTails.mp (hV hn).1).2.2.1⟩
  have sizes {p : ℕ} (hp : p ∈ W) : 5<p ∧ p ≤ X ∧ 5*p^2 ≤ X ∧
      30 ≤ (X:ℝ)/p ∧ H ≤ (X:ℝ)/p := by
    obtain ⟨hp',hl,hu⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hp
    have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp'.pos
    have h5 : (5:ℝ)<p := by linarith only [ht30,ht4,hl]
    have hpx : (p:ℝ) ≤ X := hu.trans ((hpows (by decide : 5 ≤ 16)).trans_eq h16)
    have h6 : 5 ≤ t^6 := by
      have h := hpows (by decide : 1 ≤ 6); rw [pow_one] at h; linarith only [h,ht30]
    have hs : 5*(p:ℝ)^2 ≤ X := by
      calc _ ≤ 5*(t^5)^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp0.le hu _) (by norm_num)
           _ ≤ (t^5)^2*t^6 := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
           _ = t^16 := by ring
           _ = _ := h16
    have hq : t^11 ≤ (X:ℝ)/p := (le_div_iff₀ hp0).2 (calc
      t^11*(p:ℝ) ≤ t^11*t^5 := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = t^16 := by ring
      _ = _ := h16)
    have htT : t ≤ (X:ℝ)/p := (by simpa only [pow_one] using hpows (by decide : 1 ≤ 11) : t ≤ t^11).trans hq
    exact ⟨by exact_mod_cast h5,by exact_mod_cast hpx,by exact_mod_cast hs,ht30.trans htT,
      ((le_max_right _ _).trans ht).trans htT⟩
  let D := negParity V
  have hD : D ⊆ (negParity S).filter (fun n => ¬n.Prime) := by
    intro n hn
    obtain ⟨hm,hμ⟩ := mem_filter.mp hn
    obtain ⟨hs,hp⟩ := hV hm
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hs,hμ⟩,fun h => ?_⟩
    have hpx := (sizes hp).2.1
    rw [h.minFac_eq] at hpx
    exact (mem_Ioc.mp (hVI hm)).1.not_ge hpx
  obtain ⟨A,hneg,hsrc⟩ := match_selected_triples hfour (hchild y · hfour) D hD
  have hAs : A.sources ⊆ posParity V := by
    intro n hn
    obtain ⟨m,hm,he⟩ := hsrc n hn
    obtain ⟨hs,hμ⟩ := mem_filter.mp (A.sources_subset hn)
    exact mem_filter.mpr ⟨fromS hs (he ▸ (hV (mem_filter.mp hm).1).2),hμ⟩
  have info {n : ℕ} (hn : n ∈ posParity V) :
      let N := splitLarger X n
      let p := n.minFac
      let T := (X:ℝ)/p
      N ∈ negParity (Ioc X (2*X)) ∧ N.minFac ∈ ({2,3,5}:Finset ℕ) ∧
      (N/N.minFac).minFac=p ∧ GlobalDyadicOneTwoRel n N ∧ n/p ∈ windowPrimes T (2*T) := by
    obtain ⟨hm,hμ⟩ := mem_filter.mp hn
    obtain ⟨hs,hp⟩ := hV hm
    obtain ⟨h5,_,hsmall,h30,hH'⟩ := sizes hp
    obtain ⟨a,b,ha,hb,hab,he⟩ := positive_is_semiprime hfour (mem_filter.mpr ⟨hs,hμ⟩)
    have hmin : n.minFac=a := by
      rw [he,Nat.mul_comm a b]
      exact (append_smallest hb.one_lt ha (by rwa [hb.minFac_eq])).1
    have hz : (n/n.minFac).Prime := by rw [hmin,he,Nat.mul_div_cancel_left _ ha.pos]; exact hb
    exact split_in_row (hVI hm) (mem_roughTails.mp hs).2.2.2.1 hμ (hmin ▸ ha) hz h5 hsmall (hH _ hH') h30
  refine assemble_exports hVI A hAs hneg (splitLarger X) ?_ ?_
  · intro n hn m hm he
    obtain ⟨_,_,hmi,_,hz⟩ := info hn
    obtain ⟨_,_,hmj,_,hz'⟩ := info hm
    have heq := hmi.symm.trans ((congrArg (fun k : ℕ => (k/k.minFac).minFac) he).trans hmj)
    have hp := Nat.minFac_prime (mem_roughTails.mp (hV (mem_filter.mp hn).1).1).1.ne'
    dsimp only [splitLarger] at he
    rw [←heq] at he hz'
    have hslot := Nat.eq_of_mul_eq_mul_left hp.pos he
    have hval := rankedSlot_inj (hH _ (sizes (hV (mem_filter.mp hn).1).2).2.2.2.2) hz hz' hslot
    calc n = (n/n.minFac)*n.minFac := (Nat.div_mul_cancel (Nat.minFac_dvd _)).symm
         _ = (m/n.minFac)*n.minFac := congrArg (·*n.minFac) hval
         _ = m := Nat.div_mul_cancel (heq ▸ Nat.minFac_dvd _)
  · intro n hn
    obtain ⟨hh,hsm,_,hr,_⟩ := info hn
    refine ⟨hh,fun h => ?_,hsm,hr⟩
    have hgt := (sizes (hV h).2).1
    exact hgt.not_ge (small_cofactor_cases hsm).2.2

#print axioms eventually_exact_least_prime_exports

end GaloisForLFunctions.RestrictedFactorizationCalculus
