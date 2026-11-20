import GaloisForLFunctions.SignedArithmeticCorrespondences.ThePathsInAFourfoldWeilComb
import GaloisForLFunctions.SignedArithmeticCorrespondences.WeilMassOnDilatedCombWindows

/-!
# The sharp prime-contact radius on a fourfold Weil comb

The four-site path has edge weights a,b,a. Its positive eigenvalue solves
r²=br+a². Completing squares at the two ends pays the entire path, and the
same constant pays the shorter paths. The prime weights are a=log 2 and
b=log 3.
-/

open Finset
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
noncomputable section
open scoped Classical

private def pathFamily (k : ℕ) : Finset FourfoldPath :=
  (fourfoldPairs k).image .pair ∪ (fourfoldTriples k).image .triple ∪ (fourfoldQuads k).image .quad

private theorem in_pathFamily (k : ℕ) (u : FourfoldPath) : u∈pathFamily k ↔ u.admissible k := by
  cases u <;> simp [pathFamily,FourfoldPath.admissible]

private def pathContact (a b : ℝ) (c : ℕ → ℝ) : FourfoldPath → ℝ
  | .pair x => 2*a*c x*c (2*x)
  | .triple x => 2*a*c x*c (2*x) + 2*b*c x*c (3*x)
  | .quad i => 2*a*c (2*i)*c (4*i) + 2*b*c (2*i)*c (6*i) + 2*a*c (3*i)*c (6*i)

private theorem contact_eq_sum_paths (k : ℕ) (w c : ℕ → ℝ) :
    contactTerm w (Ioc (6*k) (24*k)) c c = ∑ u ∈ pathFamily k, pathContact (w 2) (w 3) c u := by
  let A := (fourfoldPairs k).image FourfoldPath.pair
  let B := (fourfoldTriples k).image FourfoldPath.triple
  let Q := (fourfoldQuads k).image FourfoldPath.quad
  have hab : Disjoint A B := disjoint_left.mpr (by
    intro u ha hb
    obtain ⟨_,_,rfl⟩ := mem_image.mp ha
    simp [B] at hb)
  have hq : Disjoint (A∪B) Q := disjoint_left.mpr (by
    intro u hu h
    obtain ⟨_,_,rfl⟩ := mem_image.mp h
    simp [A,B] at hu)
  rw [fourfold_contact_blocks]
  change _ = ∑ u ∈ (A∪B)∪Q, _
  rw [sum_union hq,sum_union hab]
  simp only [A,B,Q,sum_image (fun _ _ _ _ h => FourfoldPath.pair.inj h),
    sum_image (fun _ _ _ _ h => FourfoldPath.triple.inj h),
    sum_image (fun _ _ _ _ h => FourfoldPath.quad.inj h),pathContact,fourfoldEdge]
  congr 1
  · congr 1 <;> exact sum_congr rfl fun _ _ => by ring
  · exact sum_congr rfl fun _ _ => by ring

/-- The largest positive eigenvalue of the path with weights log 2, log 3,
log 2. The same number is the sharp constant for the entire comb. -/
def fourfoldContactRadius : ℝ := (Real.log 3 + Real.sqrt ((Real.log 3)^2+4*(Real.log 2)^2))/2

private theorem radius_data :
    let a := Real.log 2
    let b := Real.log 3
    let r := fourfoldContactRadius
    0<a ∧ 0<b ∧ 0<r ∧ a≤r ∧ b≤r ∧ r^2=b*r+a^2 := by
  let a := Real.log 2
  let b := Real.log 3
  have ha : 0<a := Real.log_pos (by norm_num)
  have hb : 0<b := Real.log_pos (by norm_num)
  let u := Real.sqrt (b^2+4*a^2)
  have hu : 0≤u := Real.sqrt_nonneg _
  have hs : u^2=b^2+4*a^2 := Real.sq_sqrt (by positivity)
  have hab : 2*a ≤ u := (sq_le_sq₀ (by positivity) hu).mp (by nlinarith only [hs,sq_nonneg b])
  have hbu : b ≤ u := (sq_le_sq₀ hb.le hu).mp (by nlinarith only [hs,sq_nonneg a])
  change 0<a ∧ 0<b ∧ 0<(b+u)/2 ∧ a≤(b+u)/2 ∧ b≤(b+u)/2 ∧ ((b+u)/2)^2=b*((b+u)/2)+a^2
  exact ⟨ha,hb,by linarith only [hb,hu],by linarith only [hab,hb],
    by linarith only [hbu],by nlinarith only [hs]⟩

/-- Sum-of-squares certificates for all three component types. The four-site
certificate is the sum of the two endpoint squares and br(y-z)². -/
private theorem path_bound {k : ℕ} (u : FourfoldPath) (hu : u.admissible k) (c : ℕ → ℝ) :
    pathContact (Real.log 2) (Real.log 3) c u ≤
      fourfoldContactRadius * ∑ n ∈ u.sites, (c n)^2 := by
  let a := Real.log 2
  let b := Real.log 3
  let r := fourfoldContactRadius
  obtain ⟨ha,hb,hr,har,hbr,hrel⟩ := radius_data
  change r^2=b*r+a^2 at hrel
  change pathContact a b c u ≤ r * _
  cases u with
  | pair x =>
    have hx := (mem_Ioc.mp (mem_filter.mp hu).1).1
    have hn : x≠2*x := by omega
    simp only [FourfoldPath.sites,pathContact,sum_insert (notMem_singleton.mpr hn),sum_singleton]
    nlinarith only [mul_nonneg (show 0≤r-a from sub_nonneg.mpr har) (add_nonneg
      (sq_nonneg (c x)) (sq_nonneg (c (2*x)))),mul_nonneg ha.le (sq_nonneg (c x-c (2*x)))]
  | triple x =>
    have hx := (mem_Ioc.mp (mem_filter.mp hu).1).1
    have h₁ : x∉({2*x,3*x}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have h₂ : 2*x∉({3*x}:Finset ℕ) := notMem_singleton.mpr (by omega)
    simp only [FourfoldPath.sites,pathContact,sum_insert h₁,sum_insert h₂,sum_singleton]
    apply (mul_le_mul_iff_right₀ (show 0<r from hr)).mp
    have hrel' := congrArg (fun v : ℝ => v * (c x)^2) hrel
    nlinarith only [hrel',sq_nonneg (r*c (2*x)-a*c x),sq_nonneg (r*c (3*x)-b*c x),
      mul_nonneg (mul_nonneg hb.le (sub_nonneg.mpr hbr)) (sq_nonneg (c x))]
  | quad i =>
    have hi := (mem_Ioc.mp hu).1
    have h₁ : 4*i∉({2*i,6*i,3*i}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have h₂ : 2*i∉({6*i,3*i}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have h₃ : 6*i∉({3*i}:Finset ℕ) := notMem_singleton.mpr (by omega)
    simp only [FourfoldPath.sites,pathContact,sum_insert h₁,sum_insert h₂,sum_insert h₃,sum_singleton]
    apply (mul_le_mul_iff_right₀ (show 0<r from hr)).mp
    have hmid := congrArg (fun v : ℝ => v*((c (2*i))^2+(c (6*i))^2)) hrel
    nlinarith only [hmid,sq_nonneg (r*c (4*i)-a*c (2*i)),sq_nonneg (r*c (3*i)-a*c (6*i)),
      mul_nonneg (mul_nonneg hb.le hr.le) (sq_nonneg (c (2*i)-c (6*i)))]

/-- A uniform bound for the complete prime debit on (6k,24k], for every
profile on all sites, without constraints on its centered-divisibility coordinates. -/
theorem fourfold_prime_contact_le (k : ℕ) (c : ℕ → ℝ) :
    contactTerm ArithmeticFunction.vonMangoldt (Ioc (6*k) (24*k)) c c ≤
      fourfoldContactRadius*∑ n ∈ Ioc (6*k) (24*k), (c n)^2 := by
  have hd : (pathFamily k : Set FourfoldPath).PairwiseDisjoint FourfoldPath.sites :=
    fun u hu v hv huv => fourfold_path_sites_disjoint ((in_pathFamily k u).mp hu)
      ((in_pathFamily k v).mp hv) huv
  have hs : (pathFamily k).biUnion FourfoldPath.sites ⊆ Ioc (6*k) (24*k) := by
    intro n hn
    obtain ⟨u,hu,hm⟩ := mem_biUnion.mp hn
    exact fourfold_path_sites_subset ((in_pathFamily k u).mp hu) hm
  rw [contact_eq_sum_paths,ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]
  calc
    _ ≤ ∑ u ∈ pathFamily k, fourfoldContactRadius*∑ n ∈ u.sites, (c n)^2 :=
      sum_le_sum fun u hu => path_bound u ((in_pathFamily k u).mp hu) c
    _ = fourfoldContactRadius*∑ n ∈ (pathFamily k).biUnion FourfoldPath.sites, (c n)^2 := by
      rw [← mul_sum,sum_biUnion hd]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hs (fun n _ _ => sq_nonneg (c n)))
      radius_data.2.2.1.le

/-- The positive extremal profile of a four-site component. -/
def fourfoldEigenprofile (i n : ℕ) : ℝ :=
  if n=2*i ∨ n=6*i then fourfoldContactRadius
  else if n=4*i ∨ n=3*i then Real.log 2 else 0

/-- Each four-site component attains the bound by itself. Its middle two
values are r and its two outside values are log 2. -/
theorem fourfold_component_attains {k i : ℕ} (hiQ : i ∈ fourfoldQuads k) :
    let c := fourfoldEigenprofile i
    0 < ∑ n ∈ Ioc (6*k) (24*k), (c n)^2 ∧
      contactTerm ArithmeticFunction.vonMangoldt (Ioc (6*k) (24*k)) c c =
        fourfoldContactRadius * ∑ n ∈ Ioc (6*k) (24*k), (c n)^2 := by
  have hi : 0 < i := Nat.zero_lt_of_lt (mem_Ioc.mp hiQ).1
  let u := FourfoldPath.quad i
  have hu : u.admissible k := hiQ
  let a := Real.log 2
  let r := fourfoldContactRadius
  let c := fourfoldEigenprofile i
  have hc₂ : c (2*i)=r := by simp [c,r,fourfoldEigenprofile]
  have hc₆ : c (6*i)=r := by simp [c,r,fourfoldEigenprofile]
  have hc₄ : c (4*i)=a := by simp [c,a,fourfoldEigenprofile,show 4*i≠2*i by omega,show 4*i≠6*i by omega]
  have hc₃ : c (3*i)=a := by simp [c,a,fourfoldEigenprofile,show 3*i≠2*i by omega,show 3*i≠6*i by omega]
  have hzero (n : ℕ) (hn : n∉u.sites) : c n=0 := by
    simp only [u,FourfoldPath.sites,mem_insert,mem_singleton] at hn
    simp only [c,fourfoldEigenprofile,if_neg (show ¬(n=2*i ∨ n=6*i) by tauto),if_neg (show ¬(n=4*i ∨ n=3*i) by tauto)]
  have energy : ∑ n ∈ Ioc (6*k) (24*k), (c n)^2 = 2*r^2+2*a^2 := by
    rw [← sum_subset (fourfold_path_sites_subset hu) (fun n _ hn => by rw [hzero n hn,zero_pow (by decide : 2≠0)])]
    have h₁ : 4*i∉({2*i,6*i,3*i}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have h₂ : 2*i∉({6*i,3*i}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; omega
    have h₃ : 6*i∉({3*i}:Finset ℕ) := notMem_singleton.mpr (by omega)
    simp only [u,FourfoldPath.sites,sum_insert h₁,sum_insert h₂,sum_insert h₃,sum_singleton,
      hc₂,hc₃,hc₄,hc₆]
    ring
  obtain ⟨ha,_,hr,_,_,hrel⟩ := radius_data
  change 0 < ∑ n ∈ Ioc (6*k) (24*k), (c n)^2 ∧
    contactTerm ArithmeticFunction.vonMangoldt (Ioc (6*k) (24*k)) c c =
      r * ∑ n ∈ Ioc (6*k) (24*k), (c n)^2
  constructor
  · rw [energy]
    have : 0<r := hr
    positivity
  rw [contact_eq_sum_paths,ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three,sum_eq_single_of_mem u ((in_pathFamily k u).mpr hu),
    energy]
  · simp only [u,pathContact,hc₂,hc₃,hc₄,hc₆]
    change 2*a*r*a+2*Real.log 3*r*r+2*a*a*r = r*(2*r^2+2*a^2)
    change r^2=Real.log 3*r+a^2 at hrel
    linear_combination -2*r*hrel
  · intro v hv hne
    have hdis := disjoint_left.mp (fourfold_path_sites_disjoint ((in_pathFamily k v).mp hv) hu hne)
    have hz (n : ℕ) (hn : n∈v.sites) : c n=0 := hzero n (hdis hn)
    cases v with
    | pair x => simp [pathContact,hz x (by simp [FourfoldPath.sites])]
    | triple x => simp [pathContact,hz x (by simp [FourfoldPath.sites])]
    | quad j =>
      simp [pathContact,hz (2*j) (by simp [FourfoldPath.sites]),hz (3*j) (by simp [FourfoldPath.sites])]

/-- At every positive aligned scale there is an extremizing profile. -/
theorem fourfold_prime_contact_attained {k : ℕ} (hk : 0 < k) :
    ∃ c : ℕ → ℝ, 0 < ∑ n ∈ Ioc (6*k) (24*k), (c n)^2 ∧
      contactTerm ArithmeticFunction.vonMangoldt (Ioc (6*k) (24*k)) c c =
        fourfoldContactRadius * ∑ n ∈ Ioc (6*k) (24*k), (c n)^2 :=
  ⟨fourfoldEigenprofile (4*k),fourfold_component_attains (mem_Ioc.mpr ⟨by omega,le_rfl⟩)⟩

/-- A profile on the dilated comb supported on multiples of d. -/
def dilateCombProfile (d : ℕ) (c : ℕ → ℝ) (m : ℕ) : ℝ :=
  if d ∣ m then c (m/d) else 0

/-- Zero extension along common dilation preserves both the signed prime
form and the squared mass on an arbitrary interval. -/
theorem contactTerm_dilate_interval {d : ℕ} (hd : 0<d) (N U : ℕ) (w c e : ℕ → ℝ) :
    contactTerm w (Ioc (d*N) (d*U)) (dilateCombProfile d c) (dilateCombProfile d e) =
      contactTerm w (Ioc N U) c e ∧
    (∑ m ∈ Ioc (d*N) (d*U), (dilateCombProfile d c m)^2) = ∑ n ∈ Ioc N U, (c n)^2 := by
  let S := Ioc N U
  let T := Ioc (d*N) (d*U)
  let f (n : ℕ) := d*n
  let V := S.image f
  have hf : Function.Injective f := fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h
  have hsub : V ⊆ T := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hm
    exact mem_Ioc.mpr ⟨Nat.mul_lt_mul_of_pos_left (mem_Ioc.mp hn).1 hd,
      Nat.mul_le_mul_left _ (mem_Ioc.mp hn).2⟩
  have hzero (g : ℕ → ℝ) {m : ℕ} (hm : m∈T) (hv : m∉V) : dilateCombProfile d g m=0 := by
    apply if_neg
    rintro ⟨n,rfl⟩
    exact hv (mem_image.mpr ⟨n,mem_Ioc.mpr ⟨(Nat.mul_lt_mul_left hd).mp (mem_Ioc.mp hm).1,
      Nat.le_of_mul_le_mul_left (mem_Ioc.mp hm).2 hd⟩,rfl⟩)
  have heval (g : ℕ → ℝ) (n : ℕ) : dilateCombProfile d g (f n)=g n := by
    simp only [dilateCombProfile,f,dvd_mul_right,if_true,Nat.mul_div_cancel_left _ hd]
  have erase (n : ℕ) : V.erase (f n) = (S.erase n).image f := by
    ext m
    rw [mem_erase,mem_image,mem_image]
    constructor
    · rintro ⟨hne,a,ha,rfl⟩
      exact ⟨a,mem_erase.mpr ⟨fun h => hne (congrArg f h),ha⟩,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨fun h => (mem_erase.mp ha).1 (hf h),a,(mem_erase.mp ha).2,rfl⟩
  have hw (m n : ℕ) : HodgeTheoryOfAFixedPart.contactW w (f m) (f n) =
      HodgeTheoryOfAFixedPart.contactW w m n :=
    ratioContact_dilate w ⟨d,hd⟩ m n
  constructor
  · change contactTerm w T _ _ = _
    unfold contactTerm
    rw [← sum_subset hsub (fun n hn hv => sum_eq_zero (fun m _ => by rw [hzero e hn hv,mul_zero,zero_mul]))]
    change (∑ n ∈ S.image f, _) = _
    rw [sum_image hf.injOn]
    refine sum_congr rfl fun n hn => ?_
    rw [← sum_subset (erase_subset_erase (f n) hsub) (fun m hm hv => by
      have hmn := (mem_erase.mp hm).1
      have hnot : m∉V := fun h => hv (mem_erase.mpr ⟨hmn,h⟩)
      rw [hzero c (mem_erase.mp hm).2 hnot,zero_mul,zero_mul]),erase,sum_image hf.injOn]
    exact sum_congr rfl fun m _ => by rw [heval,heval,hw]
  · change (∑ m ∈ T, _) = _
    rw [← sum_subset hsub (fun m hm hv => by rw [hzero c hm hv,zero_pow (by decide : 2≠0)])]
    change (∑ m ∈ S.image f, _) = _
    rw [sum_image hf.injOn]
    exact sum_congr rfl fun n _ => by rw [heval]

/-- The sharp uniform radius applies to all fourfold combs, at every base N. -/
theorem prime_contact_fourfold_uniform (N : ℕ) (c : ℕ → ℝ) :
    contactTerm ArithmeticFunction.vonMangoldt (Ioc N (4*N)) c c ≤
      fourfoldContactRadius*∑ n ∈ Ioc N (4*N), (c n)^2 := by
  obtain ⟨hcontact,henergy⟩ := contactTerm_dilate_interval (d:=6) (by decide)
    N (4*N) ArithmeticFunction.vonMangoldt c c
  rw [show 6*(4*N)=24*N by omega] at hcontact henergy
  rw [← hcontact,← henergy]
  exact fourfold_prime_contact_le N _

private theorem dilate_six_eigenprofile (i : ℕ) :
    dilateCombProfile 6 (fourfoldEigenprofile i) = fourfoldEigenprofile (6*i) := by
  funext n
  by_cases hn : 6 ∣ n
  · obtain ⟨j,rfl⟩ := hn
    have scale (b : ℕ) : b*(6*i)=6*(b*i) := by ring
    have cancel (b : ℕ) : 6*j=6*b ↔ j=b := by omega
    simp only [dilateCombProfile,dvd_mul_right,if_true,Nat.mul_div_cancel_left _ (by decide : 0<6),
      fourfoldEigenprofile,scale,cancel]
  · have outside (b : ℕ) : n≠b*(6*i) := fun he => hn ⟨b*i,by rw [he]; ring⟩
    simp [dilateCombProfile,hn,fourfoldEigenprofile,outside]

/-- Every fourfold interval with base N≥5 attains the uniform spectral
radius. Its subgraph at 2i,3i,4i,6i is present for i=⌊N/2⌋+1. -/
theorem prime_contact_fourfold_attained {N : ℕ} (hN : 5 ≤ N) :
    ∃ c : ℕ → ℝ, 0 < ∑ n ∈ Ioc N (4*N), (c n)^2 ∧
      contactTerm ArithmeticFunction.vonMangoldt (Ioc N (4*N)) c c =
        fourfoldContactRadius * ∑ n ∈ Ioc N (4*N), (c n)^2 := by
  let i := N/2+1
  have hi : 6*i∈fourfoldQuads N := mem_Ioc.mpr (by dsimp [i]; omega)
  have h := fourfold_component_attains hi
  let c := fourfoldEigenprofile i
  obtain ⟨hc,he⟩ := contactTerm_dilate_interval (d:=6) (by decide) N (4*N)
    ArithmeticFunction.vonMangoldt c c
  exact ⟨c,by
    rw [show 6*(4*N)=24*N by omega,show dilateCombProfile 6 c=fourfoldEigenprofile (6*i)
      from dilate_six_eigenprofile i] at hc he
    simpa only [hc,he] using h⟩

/-- For a fixed width ratio the best threshold for the prime contact alone
is already forced by finite intervals. Every finite witness lifts to
arbitrarily late intervals without losing mass or changing the debit. -/
theorem eventual_prime_contact_bound_iff (Q : ℕ) (w : ℕ → ℝ) (C : ℝ) :
    (∀ᶠ N : ℕ in Filter.atTop, ∀ c : ℕ → ℝ,
      contactTerm w (Ioc N (Q*N)) c c ≤ C*∑ n ∈ Ioc N (Q*N), (c n)^2) ↔
    ∀ (N : ℕ) (c : ℕ → ℝ), contactTerm w (Ioc N (Q*N)) c c ≤
      C*∑ n ∈ Ioc N (Q*N), (c n)^2 := by
  constructor
  · intro h N c
    obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp h
    by_cases hn : N=0
    · simp [hn,contactTerm]
    let d := L+1
    have hd : 0<d := Nat.succ_pos _
    have hlate : L≤d*N := (Nat.le_succ L).trans (Nat.le_mul_of_pos_right d (Nat.pos_of_ne_zero hn))
    obtain ⟨he,hs⟩ := contactTerm_dilate_interval hd N (Q*N) w c c
    have hcomm : d*(Q*N)=Q*(d*N) := by ring
    rw [hcomm] at he hs
    simpa only [he,hs] using hL (d*N) hlate (dilateCombProfile d c)
  · exact fun h => Filter.Eventually.of_forall h

#print axioms eventual_prime_contact_bound_iff
#print axioms contactTerm_dilate_interval
#print axioms prime_contact_fourfold_attained
#print axioms prime_contact_fourfold_uniform
#print axioms fourfold_prime_contact_attained
#print axioms fourfold_prime_contact_le
end
end GaloisForLFunctions.SignedArithmeticCorrespondences
