import GaloisForLFunctions.RestrictedFactorizationCalculus.PositiveDensityOfTheTransportedDebt
import GaloisForLFunctions.RestrictedFactorizationCalculus.RoomForDisplacedPrimeTargets

/-!
# Strict gain in the number of disjoint pairs

Reassign each affected ordered row inside its own fibre, using replacement
pairs whose smaller prime exceeds the cutoff for the reserved cofactors.
The two largest-prime deletions decode the old row. The first deletion
alone separates the reserved positives from all reassigned positives.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev rowPrimes (X b : ℕ) := windowPrimes ((X:ℝ)/b) (2*((X:ℝ)/b))

private theorem scaled_cell {X b v : ℕ} (hb : 0 < b) :
    (X:ℝ)/b < v ∧ (v:ℝ) ≤ 2*((X:ℝ)/b) ↔ b*v ∈ Ioc X (2*X) := by
  have hb0 : (0:ℝ) < b := by exact_mod_cast hb
  rw [div_lt_iff₀ hb0,←mul_div_assoc,le_div_iff₀ hb0,mem_Ioc]
  constructor
  · rintro ⟨h₁,h₂⟩
    rw [mul_comm b]
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩
  · rintro ⟨h₁,h₂⟩
    rw [mul_comm b] at h₁ h₂
    exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

private def refillRoot (X b : ℕ) := ((X:ℝ)/b)^(1/16:ℝ)

private theorem refillRoot_pow (X b : ℕ) : refillRoot X b^16 = (X:ℝ)/b := by
  rw [refillRoot,←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
  norm_num

/-- Reassign the old targets. Every new positive lies above the cutoff after
deletion of its largest prime, and deleting both largest primes recovers its old row. -/
private theorem reassign_ordered {X : ℕ} {S : ℝ} (hX : 1 ≤ X) (hS0 : 0 ≤ S)
    (A : OppositeParityMatching OrderedExchange (Ioc X (2*X)))
    (hsupply : ∀ b : ℕ, 0 < b → (b:ℝ) ≤ S → S < refillRoot X b ∧
      (rowPrimes X b).card ≤ (replacementProducts (refillRoot X b)).card) :
    ∃ f : A.sources → ℕ, Function.Injective f ∧ ∀ i,
      f i ∈ posParity (Ioc X (2*X)) ∧ GlobalDyadicOneTwoRel (f i) (A.partner i) ∧
      S < (stem (f i):ℝ) := by
  let b := fun i : A.sources => evenPrefixCofactor (i:ℕ)
  -- Equal ranks reassign an old prime target within its own ordered row.
  let w := fun i : A.sources => rankedSlot (rowPrimes X (b i)) (replacementProducts (refillRoot X (b i)))
    (A.partner i / b i)
  let f := fun i : A.sources => if (b i:ℝ) ≤ S then b i*w i else (i:ℕ)
  have oldP (i : A.sources) : (i:ℕ) ∈ fibrePos X (b i) := mem_filter.mpr ⟨A.sources_subset i.property,rfl⟩
  have oldN (i : A.sources) : A.partner i ∈ fibreNeg X (b i) :=
    mem_filter.mpr ⟨A.partner_mem i i.property,(A.adj i i.property).2.symm⟩
  have prime (i : A.sources) : 0 < b i ∧ A.partner i/b i ∈ rowPrimes X (b i) ∧
      A.partner i = b i*(A.partner i/b i) := by
    obtain ⟨hb,_,p,hp,hn,_⟩ := mem_fibreNeg_structure hX (oldN i)
    have hbp := Nat.pos_of_ne_zero hb.ne_zero
    have hI : b i*p ∈ Ioc X (2*X) := hn ▸ (mem_filter.mp (A.partner_mem i i.property)).1
    rw [hn,Nat.mul_div_cancel_left _ hbp]
    exact ⟨hbp,(mem_windowPrimes (by positivity) (by positivity)).2 ⟨hp,(scaled_cell hbp).2 hI⟩,rfl⟩
  have info (i : A.sources) :
      f i ∈ posParity (Ioc X (2*X)) ∧ GlobalDyadicOneTwoRel (f i) (A.partner i) ∧
      S < (stem (f i):ℝ) ∧ stem (stem (f i))=b i := by
    obtain ⟨hb,he,q₀,r₀,hq₀,hr₀,hqr₀,heq₀,ht₀⟩ := mem_fibrePos_structure hX (oldP i)
    obtain ⟨hb0,hpwin,hpdec⟩ := prime i
    by_cases hsmall : (b i:ℝ) ≤ S
    · obtain ⟨ht,hcap⟩ := hsupply _ hb0 hsmall
      obtain ⟨q,r,hq,hr,hlo,hqr,heq,hwL,hwU⟩ := replacementProducts_factors
        (hS0.trans_lt ht) (rankedSlot_mem hcap hpwin)
      change w i=q*r at heq
      have hbq : b i < q := by exact_mod_cast (hsmall.trans_lt ht).trans hlo
      have htop : ∀ d ∈ (b i).primeFactors,d < q := fun d hd =>
        (Nat.le_of_dvd hb0 (Nat.dvd_of_mem_primeFactors hd)).trans_lt hbq
      have hI := (scaled_cell hb0).1 (by rw [←refillRoot_pow]; exact ⟨hwL,hwU⟩ :
        (X:ℝ)/b i < w i ∧ (w i:ℝ) ≤ 2*((X:ℝ)/b i))
      have hμ : μ (b i*w i)=1 := by
        rw [heq,←mul_assoc,mu_append (Nat.mul_ne_zero hb.ne_zero hq.ne_zero) hr
          (below_pair hb.ne_zero hq hqr htop),mu_append hb.ne_zero hq htop,
          moebius_eq_neg_one_pow_omega hb,he.neg_one_pow]; decide
      have hμn := (mem_filter.mp (A.partner_mem i i.property)).2
      have hp := ((mem_windowPrimes (by positivity) (by positivity)).1 hpwin).1
      rw [show f i = b i*w i from if_pos hsmall]
      refine ⟨mem_filter.mpr ⟨hI,hμ⟩,⟨squarefree_iff_moebius_ne_zero.mpr (by rw [hμ]; decide),
        (A.adj i i.property).1.2.1,by rw [hμ,hμn]; decide,b i,_,q,r,hp,hq,hr,hqr,
        Or.inr ⟨hpdec,congrArg (b i*·) heq⟩⟩,?_⟩
      rw [heq]
      obtain ⟨h₁,h₂⟩ := ordered_stems hb.ne_zero hq hr hqr htop
      exact ⟨h₁ ▸ (ht.trans hlo).trans_le (by exact_mod_cast Nat.le_mul_of_pos_left q hb0),h₂⟩
    · have hf : f i=(i:ℕ) := if_neg hsmall
      obtain ⟨h₁,h₂⟩ := ordered_stems hb.ne_zero hq₀ hr₀ hqr₀ ht₀
      have hs : S < (stem (i:ℕ):ℝ) := by
        rw [heq₀,h₁]
        exact (lt_of_not_ge hsmall).trans_le (by exact_mod_cast Nat.le_mul_of_pos_right (b i) hq₀.pos)
      refine ⟨hf ▸ A.sources_subset i.property,hf ▸ (A.adj i i.property).1,hf ▸ hs,?_⟩
      rw [hf,heq₀,h₂]
  refine ⟨f,?_,fun i => ⟨(info i).1,(info i).2.1,(info i).2.2.1⟩⟩
  intro i j hij
  have hb := (info i).2.2.2.symm.trans ((congrArg (fun n => stem (stem n)) hij).trans (info j).2.2.2)
  obtain ⟨hb0,hi,hi'⟩ := prime i
  obtain ⟨_,hj,hj'⟩ := prime j
  by_cases h : (b i:ℝ) ≤ S
  · have h' : (b j:ℝ) ≤ S := hb ▸ h
    simp only [f,if_pos h,if_pos h'] at hij
    rw [←hb] at hij hj hj'
    have heq := Nat.eq_of_mul_eq_mul_left hb0 hij
    dsimp only [w] at heq
    rw [←hb] at heq
    have hp := rankedSlot_inj (hsupply _ hb0 h).2 hi hj heq
    exact Subtype.ext (A.injOn i.property j.property (hi'.trans ((congrArg (b i*·) hp).trans hj'.symm)))
  · have h' : ¬(b j:ℝ) ≤ S := hb ▸ h
    exact Subtype.ext (by simpa only [f,if_neg h,if_neg h'] using hij)

private theorem root_above_cut {S u : ℝ} {X b k : ℕ} (hS : 1 < S) (hu : 0 ≤ u) (hb : 0 < b)
    (hsmall : (b:ℝ) ≤ S) (hX : S^24 = X) (hk : k+1 < 24) (hk0 : k ≠ 0) (hscale : u^k=(X:ℝ)/b) :
    S < u := by
  apply (pow_lt_pow_iff_left₀ (zero_lt_one.trans hS).le hu hk0).1
  rw [hscale,lt_div_iff₀ (by exact_mod_cast hb : (0:ℝ) < b),←hX]
  calc S^k*(b:ℝ) ≤ S^k*S := mul_le_mul_of_nonneg_left hsmall (pow_nonneg (zero_lt_one.trans hS).le _)
       _ = S^(k+1) := (pow_succ _ _).symm
       _ < S^24 := pow_lt_pow_right₀ hS hk

/-- Pair the entire explicit deficient family to reserved positives. The
largest-prime deletion of its image is its original small negative cofactor. -/
private theorem reserve_small {X : ℕ} {S : ℝ} (hcut : S=(X:ℝ)^(1/24:ℝ))
    (hD : deficientFamily X ⊆ negParity (Ioc X (2*X)))
    (hfit : ∀ c ∈ smallNegativeCofactors X, S < quotientRoot X c ∧ 2 ≤ quotientRoot X c ∧
      (deficientProducts (quotientRoot X c)).card ≤ (rowPrimes X c).card) :
    ∃ f : deficientFamily X → ℕ, Function.Injective f ∧ ∀ i,
      f i ∈ posParity (Ioc X (2*X)) ∧ GlobalDyadicOneTwoRel (f i) i ∧ (stem (f i):ℝ) ≤ S := by
  let C := smallNegativeCofactors X
  let W := fun c => deficientProducts (quotientRoot X c)
  have addr (i : deficientFamily X) : ∃ c ∈ C, (i:ℕ) ∈ (W c).image (c*·) := mem_biUnion.mp i.property
  let c := fun i => (addr i).choose
  have address (i : deficientFamily X) : c i ∈ C ∧ (i:ℕ) ∈ (W (c i)).image (c i*·) :=
    (addr i).choose_spec
  let w := fun i : deficientFamily X => (i:ℕ)/c i
  have row (i : deficientFamily X) : 0 < c i ∧ (c i:ℝ) ≤ S ∧ w i ∈ W (c i) ∧ c i*w i=(i:ℕ) := by
    obtain ⟨hc,hm⟩ := address i
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp (mem_filter.mp hc).1
    obtain ⟨v,hv,he⟩ := mem_image.mp hm
    have hcut' := (Nat.cast_le.mpr hhi).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) _))
    have hw : w i=v := by
      change (i:ℕ)/c i = v
      rw [←he,Nat.mul_div_cancel_left _ hlo]
    exact ⟨hlo,hcut ▸ hcut',hw ▸ hv,hw ▸ he⟩
  let p := fun i => rankedSlot (W (c i)) (rowPrimes X (c i)) (w i)
  let f := fun i => c i*p i
  have info (i : deficientFamily X) :
      f i ∈ posParity (Ioc X (2*X)) ∧ GlobalDyadicOneTwoRel (f i) i ∧ stem (f i)=c i := by
    obtain ⟨hc0,hcs,hw,hdec⟩ := row i
    obtain ⟨ht,ht2,hcap⟩ := hfit _ (address i).1
    have hpwin := rankedSlot_mem hcap hw
    obtain ⟨hp,hplo,hphi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hpwin
    have hI := (scaled_cell hc0).1 ⟨hplo,hphi⟩
    have hlt : c i < p i := by
      have hT := quotientRoot_pow X (c i)
      have hh : quotientRoot X (c i) ≤ quotientRoot X (c i)^12 := by
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith only [ht2] : 1 ≤ quotientRoot X (c i))
          (by decide : 1 ≤ 12)
      rw [hT] at hh
      exact_mod_cast (hcs.trans_lt ht).trans_le hh |>.trans hplo
    have htop : ∀ d ∈ (c i).primeFactors,d < p i := fun d hd =>
      (Nat.le_of_dvd hc0 (Nat.dvd_of_mem_primeFactors hd)).trans_lt hlt
    have hμc := (mem_filter.mp (address i).1).2
    have hμ : μ (f i)=1 := by
      change μ (c i*p i)=1
      rw [mu_append hc0.ne' hp htop,hμc]; decide
    have hμn := (mem_filter.mp (hD i.property)).2
    obtain ⟨q,r,hq,hr,hqr,_,_,heqw,_,_⟩ := deficientProducts_factors ht2 hw
    exact ⟨mem_filter.mpr ⟨hI,hμ⟩,⟨squarefree_iff_moebius_ne_zero.mpr (by rw [hμ]; decide),
      squarefree_iff_moebius_ne_zero.mpr (by rw [hμn]; decide),by rw [hμ,hμn]; decide,
      c i,p i,q,r,hp,hq,hr,hqr,Or.inl ⟨rfl,hdec.symm.trans (congrArg (c i*·) heqw)⟩⟩,
      stem_mul_of_largest hc0.ne' hp htop⟩
  refine ⟨f,?_,fun i => ⟨(info i).1,(info i).2.1,(info i).2.2 ▸ (row i).2.1⟩⟩
  intro i j hij
  have hc := (info i).2.2.symm.trans ((congrArg stem hij).trans (info j).2.2)
  change c i*p i=c j*p j at hij
  rw [←hc] at hij
  have hp := Nat.eq_of_mul_eq_mul_left (row i).1 hij
  dsimp only [p] at hp
  rw [←hc] at hp
  have hwj := (row j).2.2.1
  rw [←hc] at hwj
  have he := rankedSlot_inj (hfit (c i) (address i).1).2.2 (row i).2.2.1 hwj hp
  apply Subtype.ext
  calc (i:ℕ) = c i*w i := (row i).2.2.2.symm
       _ = c j*w j := by rw [hc,he]
       _ = (j:ℕ) := (row j).2.2.2

/-- Every sufficiently large octave admits a restricted matching retaining
all endpoints of any prescribed ordered matching, with a positive proportion
of the entire block added to its number of edges. -/
theorem eventually_strict_gain_over_ordered :
    ∀ᶠ X : ℕ in atTop, ∀ A : OppositeParityMatching OrderedExchange (Ioc X (2*X)),
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        A.sources ⊆ M.sources ∧ A.targets ⊆ M.targets ∧
        (A.sources.card:ℝ) + (X:ℝ)/49920 ≤ M.sources.card := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp eventually_replacement_capacity
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp eventually_deficientProducts_fit
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^(1/24:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_linear_deficient_family,eventually_ge_atTop 2,
    hlim.eventually_ge_atTop (max 2 (max H Z))] with X hD hX hlarge
  intro A
  let S := (X:ℝ)^(1/24:ℝ)
  have hS2 : 2 ≤ S := (le_max_left _ _).trans hlarge
  have hS1 : 1 < S := by linarith only [hS2]
  have hS24 : S^24 = X := by
    dsimp [S]; rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]; norm_num
  obtain ⟨f,hf,hfo⟩ := reassign_ordered (by omega) (zero_lt_one.trans hS1).le A (by
    intro b hb hbs
    have ht := root_above_cut hS1 (Real.rpow_nonneg (by positivity) _) hb hbs hS24
      (by decide : 16+1 < 24) (by decide : 16 ≠ 0) (refillRoot_pow X b)
    have h := hH (refillRoot X b)
      ((le_max_left _ _).trans ((le_max_right _ _).trans (hlarge.trans ht.le)))
    exact ⟨ht,by simpa only [rowPrimes,refillRoot_pow] using h⟩)
  have hneg : deficientFamily X ⊆ negParity (Ioc X (2*X)) := hD.2.trans (filter_subset _ _)
  obtain ⟨g,hg,hgo⟩ := reserve_small (X := X) (S := S) rfl hneg (by
    intro c hc
    obtain ⟨hc1,hcup⟩ := mem_Icc.mp (mem_filter.mp hc).1
    have hcS : (c:ℝ) ≤ S := (Nat.cast_le.mpr hcup).trans (Nat.floor_le (zero_lt_one.trans hS1).le)
    have ht := root_above_cut hS1 (Real.rpow_nonneg (by positivity) _) hc1 hcS hS24
      (by decide : 12+1 < 24) (by decide : 12 ≠ 0) (quotientRoot_pow X c)
    have h := hZ (quotientRoot X c)
      ((le_max_right _ _).trans ((le_max_right _ _).trans (hlarge.trans ht.le)))
    exact ⟨ht,hS2.trans ht.le,by simpa only [rowPrimes,quotientRoot_pow] using h⟩)
  have dis : Disjoint A.targets (deficientFamily X) := by
    apply disjoint_left.mpr
    intro n hn hd
    obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
    have hp : m ∈ fibrePos X (evenPrefixCofactor (A.partner m)) :=
      mem_filter.mpr ⟨A.sources_subset hm,(A.adj m hm).2⟩
    rw [(mem_filter.mp (hD.2 hd)).2] at hp
    exact notMem_empty _ hp
  let pos : A.sources ⊕ deficientFamily X → ℕ := Sum.elim f g
  let neg : A.sources ⊕ deficientFamily X → ℕ := Sum.elim (fun i => A.partner i) Subtype.val
  -- A single largest-prime deletion distinguishes the two kinds of positive endpoints.
  have sep (i : A.sources) (j : deficientFamily X) : f i ≠ g j := by
    intro he
    have hs := (hfo i).2.2
    rw [he] at hs
    exact hs.not_ge (hgo j).2.2
  have hnsep (i : A.sources) (j : deficientFamily X) : A.partner i ≠ j := by
    intro he
    exact disjoint_left.mp dis (mem_image_of_mem _ i.property) (he ▸ j.property)
  obtain ⟨G,_,htar⟩ := matching_of_indexed_edges pos neg (by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (hf h)
    · exact False.elim (sep i j' h)
    · exact False.elim (sep i' j h.symm)
    · exact congrArg Sum.inr (hg h)) (by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (Subtype.ext (A.injOn i.property i'.property h))
    · exact False.elim (hnsep i j' h)
    · exact False.elim (hnsep i' j h.symm)
    · exact congrArg Sum.inr (Subtype.ext h)) (by
    rintro (i | j)
    · exact ⟨(hfo i).1,A.partner_mem _ i.property,(hfo i).2.1⟩
    · exact ⟨(hgo j).1,hneg j.property,(hgo j).2.1⟩)
  -- Recover the old positives while retaining every negative of the larger construction.
  obtain ⟨M,ha,ht,_⟩ := combine_matchings (globalMatching A) G
  have hall : A.targets ∪ deficientFamily X ⊆ M.targets := by
    intro n hn
    apply ht
    rw [htar]
    rcases mem_union.mp hn with hn | hn
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp hn
      exact mem_image.mpr ⟨.inl ⟨m,hm⟩,mem_univ _,rfl⟩
    · exact mem_image.mpr ⟨.inr ⟨n,hn⟩,mem_univ _,rfl⟩
  have hcard := card_le_card hall
  rw [card_union_of_disjoint dis,A.card_targets,M.card_targets] at hcard
  have hc : (A.sources.card:ℝ)+(deficientFamily X).card ≤ M.sources.card := by exact_mod_cast hcard
  exact ⟨M,ha,subset_union_left.trans hall,by linarith only [hD.1,hc]⟩

/-- The actual unmatched set shrinks by at least a fixed proportion of the
octave, with every surviving integer drawn from the original unmatched set. -/
theorem eventually_linear_reduction_of_ordered_debt :
    ∀ᶠ X : ℕ in atTop, ∀ A : OppositeParityMatching OrderedExchange (Ioc X (2*X)),
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        M.unmatchedSet ⊆ A.unmatchedSet ∧
        (M.unmatchedSet.card:ℝ) + (X:ℝ)/24960 ≤ A.unmatchedSet.card := by
  filter_upwards [eventually_strict_gain_over_ordered] with X hX
  intro A
  obtain ⟨M,ha,ht,hg⟩ := hX A
  have hm : A.matchedSet ⊆ M.matchedSet := union_subset_union ha ht
  have total {R : ℕ → ℕ → Prop} (C : OppositeParityMatching R (Ioc X (2*X))) :
      (C.unmatchedSet.card:ℝ) + 2 * C.sources.card = (squarefreeOf (Ioc X (2*X))).card := by
    have h := card_sdiff_add_card_eq_card C.matchedSet_subset
    change C.unmatchedSet.card + C.matchedSet.card = _ at h
    rw [C.card_matchedSet] at h
    exact_mod_cast h
  refine ⟨M,fun n hn => mem_sdiff.mpr ⟨(mem_sdiff.mp hn).1,fun h => (mem_sdiff.mp hn).2 (hm h)⟩,?_⟩
  linarith only [total A,total M,hg]

/-- Full evacuation and linear gain can be achieved in the same matching.
Every old positive endpoint is retained while all empty-fibre negatives,
at every factor count, are matched simultaneously. -/
theorem eventually_linear_gain_covering_all_empty :
    ∀ᶠ X : ℕ in atTop, ∀ A : OppositeParityMatching OrderedExchange (Ioc X (2*X)),
      ∃ M : OppositeParityMatching GlobalDyadicOneTwoRel (Ioc X (2*X)),
        A.sources ⊆ M.sources ∧
        (negParity (Ioc X (2*X))).filter (fun n => fibrePos X (evenPrefixCofactor n)=∅) ⊆ M.targets ∧
        (A.sources.card:ℝ) + (X:ℝ)/49920 ≤ M.sources.card := by
  filter_upwards [eventually_strict_gain_over_ordered,eventually_every_empty_fibre_covered] with X hg he
  intro A
  obtain ⟨G,hA,_,hgain⟩ := hg A
  obtain ⟨E,_,hcov⟩ := he A
  obtain ⟨M,hG,hE,_⟩ := combine_matchings G E
  exact ⟨M,hA.trans hG,hcov.trans hE,hgain.trans (by exact_mod_cast card_le_card hG)⟩

#print axioms eventually_strict_gain_over_ordered
#print axioms eventually_linear_reduction_of_ordered_debt
#print axioms eventually_linear_gain_covering_all_empty

end GaloisForLFunctions.RestrictedFactorizationCalculus
