import GaloisForLFunctions.RHTower.EulerDeletionMobiusGramCancellation
import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder

/-!
# Dilation-separated prefixes force power-law current growth

The exact arithmetic prefix is a scalar multiple of a growing power sum minus
one. One scalar cannot suppress two sufficiently separated dilation scales.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionDilationGrowth
open DeletionMixedRefinement DeletionMobiusCurrent DeletionReflectedEnergy

/-- The actual power-sum prefix has its nonzero normalized strip limit. -/
theorem rawPrefix_mul_cpow_tendsto {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (fun K : ℕ => rawPrefix s K*(K : ℂ)^(s-1)) atTop (nhds (1/(1-s))) := by
  have hs1 : s≠1 := by intro h; simp [h] at hs'
  have hp := tendsto_nat_cpow_zero (z := s-1) (by simp; linarith)
  have hk : Tendsto (kernel s) atTop (nhds 0) :=
    tendsto_nat_cpow_zero (z := -s) (by simp; linarith)
  have hc := (tendsto_centeredPowerPrefix (by linarith) hs1).add (hk.div_const 2)
  have hc' : Tendsto (fun K : ℕ => rawPrefix s K-(K : ℂ)^(1-s)/(1-s))
      atTop (nhds (riemannZeta s)) := by
    simpa only [zero_div,add_zero,sub_add_cancel] using hc
  have ht := (hc'.mul hp).add_const (1/(1-s))
  simp only [mul_zero,zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hK0 : (K : ℂ)≠0 := by exact_mod_cast (show K≠0 by omega)
  have hm : (K : ℂ)^(1-s)*(K : ℂ)^(s-1)=1 := by
    rw [← Complex.cpow_add _ _ hK0,show 1-s+(s-1)=0 by ring,Complex.cpow_zero]
  calc _ = rawPrefix s K*(K : ℂ)^(s-1)-
      ((K : ℂ)^(1-s)*(K : ℂ)^(s-1))/(1-s)+1/(1-s) := by ring
       _ = _ := by rw [hm]; ring

/-- Magnitudes retain their positive power-law leading coefficient. -/
theorem rawPrefix_norm_div_rpow_tendsto {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    Tendsto (fun K : ℕ => ‖rawPrefix s K‖/(K : ℝ)^(1-s.re)) atTop
      (nhds ‖1/(1-s)‖) := by
  apply (rawPrefix_mul_cpow_tendsto hs hs').norm.congr'
  filter_upwards [eventually_ge_atTop 1] with K hK
  rw [norm_mul,Complex.norm_natCast_cpow_of_pos (by omega)]
  simp only [Complex.sub_re,Complex.one_re]
  rw [show s.re-1= -(1-s.re) by ring,Real.rpow_neg (Nat.cast_nonneg K)]
  rfl

/-- One fixed integer dilation eventually doubles every power-sum magnitude. -/
theorem exists_rawPrefix_dilation_separation {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    ∃ D K₀ : ℕ, 2≤D ∧ 1≤K₀ ∧ ∀ K : ℕ, K₀≤K →
      2*‖rawPrefix s K‖≤‖rawPrefix s (D*K)‖ := by
  let A : ℝ := ‖1/(1-s)‖
  have hA : 0<A := by
    dsimp [A]
    apply norm_pos_iff.mpr
    apply one_div_ne_zero
    intro h
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  have hlim := rawPrefix_norm_div_rpow_tendsto hs hs'
  have he : ∀ᶠ K : ℕ in atTop, 1≤K ∧
      A/2≤‖rawPrefix s K‖/(K : ℝ)^(1-s.re) ∧
      ‖rawPrefix s K‖/(K : ℝ)^(1-s.re)≤2*A := by
    filter_upwards [eventually_ge_atTop 1,
      hlim.eventually (eventually_gt_nhds (show A/2<A by linarith)),
      hlim.eventually (eventually_lt_nhds (show A<2*A by linarith))] with K hK hlo hhi
    exact ⟨hK,hlo.le,hhi.le⟩
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp he
  have hg : Tendsto (fun D : ℕ => (D : ℝ)^(1-s.re)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0<1-s.re)).comp tendsto_natCast_atTop_atTop
  obtain ⟨D,hD,hpow⟩ := ((eventually_ge_atTop 2).and (hg.eventually_ge_atTop 8)).exists
  refine ⟨D,K₀,hD,(hK₀ K₀ le_rfl).1,?_⟩
  intro K hK
  have hDK : K₀≤D*K := hK.trans (by nlinarith)
  obtain ⟨hK1,hlo,hhi⟩ := hK₀ K hK
  obtain ⟨hDK1,hloD,hhiD⟩ := hK₀ (D*K) hDK
  have hKpos : (0 : ℝ)<K := by exact_mod_cast hK1
  have hDKpos : (0 : ℝ)<((D*K : ℕ) : ℝ) := by exact_mod_cast hDK1
  have hu := (div_le_iff₀ (Real.rpow_pos_of_pos hKpos _)).mp hhi
  have hl := (le_div_iff₀ (Real.rpow_pos_of_pos hDKpos _)).mp hloD
  rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg D) (Nat.cast_nonneg K)] at hl
  have hx : 0≤(K : ℝ)^(1-s.re) := Real.rpow_nonneg hKpos.le _
  nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg hA.le hx)]

/-- No complex scalar can suppress both magnitude-separated prefixes. -/
theorem scalar_pair_energy_lower {x y : ℂ} (hxy : 2*‖x‖≤‖y‖) (h : ℂ) :
    (1 : ℝ)/8≤‖h*x-1‖^2+‖h*y-1‖^2 := by
  have hx : 1≤‖h*x-1‖+‖h*x‖ := by
    simpa only [sub_sub_cancel,norm_one,add_comm] using norm_sub_le (h*x) (h*x-1)
  have hy : ‖h*y‖≤‖h*y-1‖+1 := by
    simpa only [sub_add_cancel,norm_one] using norm_add_le (h*y-1) (1 : ℂ)
  have hm : 2*‖h*x‖≤‖h*y‖ := by
    simp only [norm_mul]
    nlinarith [mul_le_mul_of_nonneg_left hxy (norm_nonneg h)]
  have hh : 1≤2*‖h*x-1‖+‖h*y-1‖ := by linarith
  nlinarith [sq_nonneg (2*‖h*x-1‖-‖h*y-1‖),sq_nonneg (‖h*y-1‖),
    mul_self_le_mul_self (by norm_num : (0 : ℝ)≤1) hh]

private theorem sourcePrefix_initial_raw {N K : ℕ} (hK : 0<K) (hKN : K≤N) (s : ℂ) :
    sourcePrefix N s K=(deningerHarmonicPartial N : ℂ)*rawPrefix s K-1 := by
  rw [sourcePrefix_initial hK hKN s]
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  simp [DeletionChronologicalLimit.kernel,kernel]

/-- The literal source retains a uniform two-scale defect independently of harmonic size. -/
theorem exists_sourcePrefix_dilation_pair_lower {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    ∃ D K₀ : ℕ, 2≤D ∧ 1≤K₀ ∧ ∀ N K : ℕ, K₀≤K → D*K≤N →
      (1 : ℝ)/8≤‖sourcePrefix N s K‖^2+‖sourcePrefix N s (D*K)‖^2 := by
  obtain ⟨D,K₀,hD,hK₀,hsep⟩ := exists_rawPrefix_dilation_separation hs hs'
  refine ⟨D,K₀,hD,hK₀,?_⟩
  intro N K hK hKN
  have hK1 : 0<K := by omega
  have hDK1 : 0<D*K := Nat.mul_pos (by omega) hK1
  rw [sourcePrefix_initial_raw hK1 (by nlinarith) s,sourcePrefix_initial_raw hDK1 hKN s]
  exact scalar_pair_energy_lower (hsep K hK) _

/-- Pairing with an injective dilation uses each nonnegative coordinate at most twice. -/
theorem sum_prefix_lower_of_dilation_pairs {f : ℕ → ℝ} (hf : ∀ k, 0≤f k)
    {D K₀ N : ℕ} (hD : 2≤D) (hK₀ : 1≤K₀) (hN : 2*D*(K₀+1)≤N)
    (hpair : ∀ K, K₀≤K → D*K≤N → (1 : ℝ)/8≤f K+f (D*K)) :
    (N : ℝ)/(64*(D : ℝ))≤∑ k ∈ Finset.Icc 1 N, f k := by
  let R := N/D
  let S := Finset.Icc K₀ R
  let T := ∑ k ∈ Finset.Icc 1 N, f k
  have hD0 : 0<D := by omega
  have hR : 2*(K₀+1)≤R := by
    apply (Nat.le_div_iff_mul_le hD0).mpr
    nlinarith
  have hRN : R≤N := Nat.div_le_self N D
  have hDN : D*R≤N := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self N D
  have hNR : N≤2*D*R := by
    have hlt : N<(R+1)*D := (Nat.div_lt_iff_lt_mul hD0).mp (Nat.lt_succ_self R)
    nlinarith
  have hS : S⊆Finset.Icc 1 N := by
    intro k hk
    obtain ⟨hk0,hkR⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hK₀.trans hk0,hkR.trans hRN⟩
  have hDS : S.image (fun k => D*k)⊆Finset.Icc 1 N := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hj0,hjR⟩ := Finset.mem_Icc.mp hj
    apply Finset.mem_Icc.mpr
    constructor
    · nlinarith
    · exact (Nat.mul_le_mul_left D hjR).trans hDN
  have hs1 : (∑ k ∈ S, f k)≤T :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun k _ _ => hf k)
  have hs2 : (∑ k ∈ S, f (D*k))≤T := by
    have hinj : Set.InjOn (fun k : ℕ => D*k) S := by
      intro i hi j hj hij
      exact Nat.eq_of_mul_eq_mul_left hD0 hij
    rw [← Finset.sum_image hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hDS (fun k _ _ => hf k)
  have hp : (S.card : ℝ)/8≤(∑ k ∈ S, f k)+(∑ k ∈ S, f (D*k)) := by
    calc _ = ∑ _k ∈ S, (1 : ℝ)/8 := by simp [div_eq_mul_inv]
         _ ≤ ∑ k ∈ S, (f k+f (D*k)) := by
           apply Finset.sum_le_sum
           intro k hk
           obtain ⟨hk0,hkR⟩ := Finset.mem_Icc.mp hk
           exact hpair k hk0 ((Nat.mul_le_mul_left D hkR).trans hDN)
         _ = _ := Finset.sum_add_distrib
  have hcard : R≤2*S.card := by
    simp only [S,Nat.card_Icc]
    omega
  have hcardR : (R : ℝ)≤2*(S.card : ℝ) := by exact_mod_cast hcard
  have hsum : (R : ℝ)≤32*T := by linarith
  have hNR' : (N : ℝ)≤2*(D : ℝ)*(R : ℝ) := by exact_mod_cast hNR
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<64*(D : ℝ))).mpr
  have hm := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ)≤2*(D : ℝ) by positivity)
  dsimp [T] at *
  nlinarith

/-- Initial prefix energy has linear mass uniformly in the cutoff harmonic scalar. -/
theorem exists_sourcePrefix_square_sum_linear_lower {s : ℂ} (hs : 0<s.re) (hs' : s.re<1) :
    ∃ D : ℕ, 2≤D ∧ ∀ᶠ N : ℕ in atTop,
      (N : ℝ)/(64*(D : ℝ))≤∑ k ∈ Finset.Icc 1 N, ‖sourcePrefix N s k‖^2 := by
  obtain ⟨D,K₀,hD,hK₀,hpair⟩ := exists_sourcePrefix_dilation_pair_lower hs hs'
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_ge_atTop (2*D*(K₀+1))] with N hN
  exact sum_prefix_lower_of_dilation_pairs (fun k => sq_nonneg _) hD hK₀ hN (hpair N)

private theorem rpow_increment_lower {a x : ℝ} (ha : 0≤a) (ha' : a≤1) (hx : 0<x) :
    a*(x+1)^(a-1)≤(x+1)^a-x^a := by
  have hy : 0<x+1 := by linarith
  have hr : -1≤ -1/(x+1) := by
    apply (le_div_iff₀ hy).mpr
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hr ha ha'
  have hbase : 0≤1+ -1/(x+1) := by linarith
  have hprod : (x+1)*(1+ -1/(x+1))=x := by field_simp; ring
  have he : x^a=(x+1)^a*(1+ -1/(x+1))^a := by
    rw [← Real.mul_rpow hy.le hbase,hprod]
  have h := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hy.le a)
  rw [← he] at h
  have halg : (x+1)^a*(1+a*(-1/(x+1))) = (x+1)^a-a*((x+1)^a/(x+1)) := by ring
  rw [halg] at h
  rw [Real.rpow_sub_one hy.ne']
  linarith

/-- Concavity gives a lower bound for every retained chronological weight increment. -/
theorem weight_increment_lower {s : ℂ} (hs : 1/2<s.re) (hs' : s.re<1)
    {N n : ℕ} (hn : n<N) :
    exponent s*((N : ℝ)+1)^(exponent s-1)≤weight s (n+1)-weight s n := by
  have ha : 0≤exponent s := by unfold exponent; linarith
  have ha' : exponent s≤1 := by unfold exponent; linarith
  have hb := rpow_increment_lower ha ha' (by positivity : (0 : ℝ)<(n : ℝ)+1)
  have hle : (n : ℝ)+1+1≤(N : ℝ)+1 := by exact_mod_cast (show n+1+1≤N+1 by omega)
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ)<(n : ℝ)+1+1)
    hle (by linarith : exponent s-1≤0)
  have h := (mul_le_mul_of_nonneg_left hpow ha).trans hb
  simpa only [weight,Nat.cast_add,Nat.cast_one,add_assoc] using h

/-- The actual initial Gram head controls all its prefix squares with the critical weight. -/
theorem energyHead_lower_prefix_sum {s : ℂ} (hs : 1/2<s.re) (hs' : s.re<1) (N : ℕ) :
    exponent s*((N : ℝ)+1)^(exponent s-1)*
      (∑ k ∈ Finset.Icc 1 N, ‖sourcePrefix N s k‖^2)≤energyHead N s N := by
  have hshift (f : ℕ → ℝ) (M : ℕ) :
      (∑ k ∈ Finset.Icc 1 M, f k)=∑ n ∈ Finset.range M, f (n+1) := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_range_succ,ih]
  have he := hshift (fun k => ‖sourcePrefix N s k‖^2) N
  rw [he,Finset.mul_sum,energyHead]
  apply Finset.sum_le_sum
  intro n hn
  have h := mul_le_mul_of_nonneg_right (weight_increment_lower hs hs' (Finset.mem_range.mp hn))
    (sq_nonneg ‖sourcePrefix N s (n+1)‖)
  exact h

/-- Every right-half zero forces a genuine cutoff-power floor for the complete current. -/
theorem exists_sourceCurrent_rpow_lower (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : 1/2<rho.1.re) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      C*(N : ℝ)^(2*rho.1.re-1)≤(sourceCurrent N rho.1).re := by
  have hs0 := RiemannGaussian.NontrivialZetaZero.zero_lt_re rho
  have hs1 := RiemannGaussian.NontrivialZetaZero.re_lt_one rho
  obtain ⟨D,hD,hbound⟩ := exists_sourcePrefix_square_sum_linear_lower hs0 hs1
  let a := exponent rho.1
  have ha : 0<a := by dsimp [a,exponent]; linarith
  have hDpos : (0 : ℝ)<D := by exact_mod_cast (show 0<D by omega)
  refine ⟨a/(128*(D : ℝ)),by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with N hsum hN
  have hNpos : (0 : ℝ)<N := by exact_mod_cast hN
  have htail := energyHead_lower_prefix_sum hs hs1 N
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0≤a*((N : ℝ)+1)^(a-1) by positivity)
  have hhalf : (N : ℝ)/((N : ℝ)+1)≥1/2 := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hN1 : (1 : ℝ)≤N := by exact_mod_cast hN
    linarith
  have hid : a*((N : ℝ)+1)^(a-1)*((N : ℝ)/(64*(D : ℝ))) =
      a/(64*(D : ℝ))*((N : ℝ)+1)^a*((N : ℝ)/((N : ℝ)+1)) := by
    rw [Real.rpow_sub_one (by positivity)]
    ring
  have hpow : (N : ℝ)^a≤((N : ℝ)+1)^a :=
    Real.rpow_le_rpow hNpos.le (by linarith) ha.le
  have hlow : a/(128*(D : ℝ))*(N : ℝ)^a≤
      a*((N : ℝ)+1)^(a-1)*((N : ℝ)/(64*(D : ℝ))) := by
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hhalf
      (show 0≤a/(64*(D : ℝ))*((N : ℝ)+1)^a by positivity)
    have hp := mul_le_mul_of_nonneg_left hpow (show 0≤a/(128*(D : ℝ)) by positivity)
    calc _ ≤ a/(128*(D : ℝ))*((N : ℝ)+1)^a := hp
         _ = a/(64*(D : ℝ))*((N : ℝ)+1)^a*(1/2) := by ring
         _ ≤ _ := hh
  have hcurrent := DeletionMixedCurrent.mixed_energy_prefix_le_current
    (Finset.range N) coefficient rho hs.le N
  exact hlow.trans (hmul.trans (htail.trans hcurrent))

/-- Reflection gives the exact horizontal-excess exponent on either side of the line. -/
theorem exists_abs_sourceCurrent_rpow_lower (rho : RiemannGaussian.NontrivialZetaZero)
    (hs : rho.1.re≠1/2) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      C*(N : ℝ)^(2*|rho.1.re-1/2|)≤|(sourceCurrent N rho.1).re| := by
  have hright (r : RiemannGaussian.NontrivialZetaZero) (hr : 1/2<r.1.re) :
      ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
        C*(N : ℝ)^(2*r.1.re-1)≤|(sourceCurrent N r.1).re| := by
    obtain ⟨C,hC,hbound⟩ := exists_sourceCurrent_rpow_lower r hr
    exact ⟨C,hC,hbound.mono (fun N hN => hN.trans (le_abs_self _))⟩
  rcases lt_or_gt_of_ne hs with hleft | hright'
  · let r := RiemannGaussian.NontrivialZetaZero.conjugatePartner rho
    have hr : r.1=DeletionReflectedGram.partner rho.1 := rfl
    have hre : r.1.re=1-rho.1.re := by
      rw [hr]
      simp [DeletionReflectedGram.partner]
    have hhalf : 1/2<r.1.re := by rw [hre]; linarith
    obtain ⟨C,hC,hbound⟩ := hright r hhalf
    have hexp : 2*r.1.re-1=2*|rho.1.re-1/2| := by
      rw [hre,abs_of_neg (by linarith : rho.1.re-1/2<0)]
      ring
    refine ⟨C,hC,?_⟩
    rw [hexp] at hbound
    simpa only [hr,sourceCurrent_partner,Complex.neg_re,abs_neg] using hbound
  · obtain ⟨C,hC,hbound⟩ := hright rho hright'
    have hexp : 2*rho.1.re-1=2*|rho.1.re-1/2| := by
      rw [abs_of_pos (by linarith : 0<rho.1.re-1/2)]
      ring
    exact ⟨C,hC,by simpa only [hexp] using hbound⟩

private theorem no_cofinal_subpower_of_power_floor {F : ℕ → ℝ} {a C : ℝ}
    (ha : 0<a) (hC : 0<C) (hlow : ∀ᶠ N : ℕ in atTop, C*(N : ℝ)^a≤F N)
    (hupper : ∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧ F N≤B*(N : ℝ)^e) :
    False := by
  obtain ⟨B,hB⟩ := hupper (a/2) (by linarith)
  have hg : Tendsto (fun N : ℕ => (N : ℝ)^(a/2)*C) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0<a/2)).comp tendsto_natCast_atTop_atTop).atTop_mul_const hC
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    (hlow.and ((hg.eventually_gt_atTop B).and (eventually_ge_atTop 1)))
  obtain ⟨N,hKN,hN⟩ := hB K
  obtain ⟨hlo,hgt,hN1⟩ := hK N hKN
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN1
  have hp : (N : ℝ)^a=(N : ℝ)^(a/2)*(N : ℝ)^(a/2) := by
    rw [← Real.rpow_add hNp]
    congr 1
    ring
  have hstrict : B*(N : ℝ)^(a/2)<C*(N : ℝ)^a := by
    rw [hp]
    have h := mul_lt_mul_of_pos_right hgt (Real.rpow_pos_of_pos hNp (a/2))
    nlinarith
  exact (not_lt_of_ge (hlo.trans hN)) hstrict

/-- A zero-dependent cofinal subpower ceiling is already an exact critical-line criterion. -/
theorem sourceCurrent_cofinally_subpower_iff (rho : RiemannGaussian.NontrivialZetaZero) :
    (∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
      |(sourceCurrent N rho.1).re|≤B*(N : ℝ)^e) ↔ rho.1.re=1/2 := by
  constructor
  · intro hu
    by_contra hr
    obtain ⟨C,hC,hbound⟩ := exists_abs_sourceCurrent_rpow_lower rho hr
    apply no_cofinal_subpower_of_power_floor
      (show 0<2*|rho.1.re-1/2| by positivity) hC hbound hu
  · intro hr e he
    refine ⟨0,fun K => ⟨K,le_rfl,?_⟩⟩
    rw [sourceCurrent,DeletionMixedCurrent.quadraticCurrent_of_re_half _ _ hr]
    simp

/-- The complete literal-current RH receiver requires only cofinal subpower growth. -/
theorem riemannHypothesis_iff_mobius_current_cofinally_subpower :
    RiemannHypothesis ↔ ∀ rho : RiemannGaussian.NontrivialZetaZero,
      ∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
        |(sourceCurrent N rho.1).re|≤B*(N : ℝ)^e := by
  constructor
  · intro hRH rho
    exact (sourceCurrent_cofinally_subpower_iff rho).mpr (hRH rho.1 rho.2.1 rho.2.2.1 rho.2.2.2)
  · intro h s hz ht hs1
    let rho : RiemannGaussian.NontrivialZetaZero := ⟨s,hz,ht,hs1⟩
    exact (sourceCurrent_cofinally_subpower_iff rho).mp (h rho)

/-- Full arithmetic input energy needs only a cofinal subpower ceiling; no RH converse is asserted. -/
theorem riemannHypothesis_of_cofinally_subpower_primitiveEnergy
    (hsource : ∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
      DeletionMobiusPrimitive.primitiveEnergy N≤B*(N : ℝ)^e) : RiemannHypothesis := by
  apply riemannHypothesis_iff_mobius_current_cofinally_subpower.mpr
  intro rho e he
  obtain ⟨C,hC,hcurrent⟩ := DeletionMobiusPrimitive.exists_current_bound_by_primitiveEnergy rho
  obtain ⟨B,hB⟩ := hsource e he
  refine ⟨C*B,fun K => ?_⟩
  obtain ⟨N,hKN,hN⟩ := hB K
  refine ⟨N,hKN,(hcurrent N).trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN hC.le

/-- The existing modular carrier has the same sufficient cofinal subpower target. -/
theorem riemannHypothesis_of_cofinally_subpower_modular_norm
    (hsource : ∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
      ‖bdMobiusModularApproximantVec N‖^2≤B*(N : ℝ)^e) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinally_subpower_primitiveEnergy
  intro e he
  obtain ⟨B,hB⟩ := hsource e he
  refine ⟨2*B,fun K => ?_⟩
  obtain ⟨N,hKN,hN⟩ := hB K
  refine ⟨N,hKN,(DeletionMobiusPrimitive.primitiveEnergy_le_two_modular_norm_sq N).trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ)≤2)

/-- A one-sided cofinal subpower bound on the complete signed cross sum suffices. -/
theorem riemannHypothesis_of_cofinally_subpower_cross
    (hsource : ∀ e : ℝ, 0<e → ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K≤N ∧
      DeletionMobiusGram.cross N≤B*(N : ℝ)^e) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinally_subpower_modular_norm
  intro e he
  obtain ⟨B,hB⟩ := hsource e he
  have hlog := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (burnolEventually_log_pow_le_rpow he 1)
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp (DeletionMobiusGram.diagonal_eventually_le_four_log.and hlog)
  refine ⟨B+4,fun K => ?_⟩
  obtain ⟨N,hKN,hcross⟩ := hB (max K K₀)
  obtain ⟨hdiag,hpow⟩ := hK₀ N ((le_max_right _ _).trans hKN)
  refine ⟨N,(le_max_left _ _).trans hKN,?_⟩
  rw [DeletionMobiusGram.modular_norm_sq_eq_diagonal_add_cross]
  simp only [pow_one] at hpow
  nlinarith

end RHTower.DeletionDilationGrowth
