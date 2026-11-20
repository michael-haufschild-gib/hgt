import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheLowerCountingOrderOfMertensExcursions
import GaloisForLFunctions.RHTower.MobiusIntegerCuspConfinement

/-!
# Packing one-sign intervals under the Mertens graph

The persistence step in De Nitti–Ignat–Quirós (arXiv:2611.22679,
Lemma 3.8) spreads a large value over a level set using an increment
bound. Mertens increments have modulus at most one. Combined with the
lower counting order of the Mertens excursions this gives, at *every*
large cutoff, the optimal counting exponent for disjoint aligned
intervals on which all values exceed a power with the same sign.
-/

noncomputable section
open Filter Finset
open scoped Topology
open _root_.RHTower GaloisForLFunctions.ArithmeticPowerMass
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem mertens_add_diff (a r : ℕ) :
    |shiftedMertensReal (a+r)-shiftedMertensReal a| ≤ r := by
  rw [shiftedMertensReal,shiftedMertensReal,sum_range_add,add_sub_cancel_left]
  have h := abs_sum_le_sum_abs (fun i => shiftedMobiusRealCoefficient (a+i)) (range r)
  exact h.trans ((sum_le_sum fun i _ => abs_shiftedMobiusRealCoefficient_le_one (a+i)).trans_eq (by simp))

private theorem mertens_index_distance (i k : ℕ) :
    |shiftedMertensReal i-shiftedMertensReal k| ≤ |(i:ℝ)-k| := by
  wlog h : k ≤ i generalizing i k
  · rw [abs_sub_comm,abs_sub_comm (i:ℝ)]
    exact this k i (le_of_not_ge h)
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le h
  simpa only [Nat.cast_add,add_sub_cancel_left,abs_of_nonneg (Nat.cast_nonneg r)] using mertens_add_diff k r

/-- Full aligned blocks inside [0,N] on which the signed threshold H
holds throughout, with either sign allowed for each block. -/
def signedMertensBlocks (L N : ℕ) (H : ℝ) : Finset ℕ :=
  (range ((N+1)/L)).filter fun j =>
    (∀ i∈Ico (j*L) ((j+1)*L), H < shiftedMertensReal i) ∨
    (∀ i∈Ico (j*L) ((j+1)*L), shiftedMertensReal i < -H)

private theorem same_block {j k L : ℕ} (hk : k∈Ico (j*L) ((j+1)*L)) {H : ℝ}
    (hhigh : H+L < |shiftedMertensReal k|) :
    (∀ i∈Ico (j*L) ((j+1)*L), H < shiftedMertensReal i) ∨
    (∀ i∈Ico (j*L) ((j+1)*L), shiftedMertensReal i < -H) := by
  have hclose (i : ℕ) (hi : i∈Ico (j*L) ((j+1)*L)) :
      |shiftedMertensReal i-shiftedMertensReal k| ≤ L := by
    obtain ⟨ha,hb⟩ := mem_Ico.mp hi
    obtain ⟨hc,hd⟩ := mem_Ico.mp hk
    simp only [Nat.add_mul,one_mul] at hb hd
    have hx : i ≤ k+L := by omega
    have hy : k ≤ i+L := by omega
    refine (mertens_index_distance i k).trans (abs_le.mpr ⟨?_,?_⟩)
    · have := (Nat.cast_le (α:=ℝ)).mpr hy
      push_cast at this
      linarith
    · have := (Nat.cast_le (α:=ℝ)).mpr hx
      push_cast at this
      linarith
  rcases le_total 0 (shiftedMertensReal k) with h | h
  · rw [abs_of_nonneg h] at hhigh
    exact Or.inl fun i hi => by linarith only [hhigh,(abs_le.mp (hclose i hi)).1]
  · rw [abs_of_nonpos h] at hhigh
    exact Or.inr fun i hi => by linarith only [hhigh,(abs_le.mp (hclose i hi)).2]

/-- Counting high prefixes costs one initial segment and at most one
incomplete last block. Every intervening occupied block has fixed sign. -/
theorem mertens_excursion_block_count {E : Finset ℕ} {L N J : ℕ} (hL : 0 < L) {H : ℝ}
    (he : ∀ k∈E, k ≤ N) (hh : ∀ k∈E, J ≤ k → H+L < |shiftedMertensReal k|) :
    E.card ≤ J+((signedMertensBlocks L N H).card+1)*L := by
  classical
  let U := insert ((N+1)/L) (signedMertensBlocks L N H)
  let cell := fun j => Ico (j*L) ((j+1)*L)
  have hsub : E ⊆ range J ∪ U.biUnion cell := by
    intro k hk
    by_cases h : k < J
    · exact mem_union_left _ (mem_range.mpr h)
    let j := k/L
    have hcell : k∈cell j := by
      refine mem_Ico.mpr ⟨Nat.div_mul_le_self _ _,?_⟩
      have hmod := Nat.mod_lt k hL
      have hdecomp := Nat.mod_add_div k L
      dsimp only [j]
      rw [Nat.add_mul,one_mul,Nat.mul_comm (k/L)]
      omega
    have hj : j ≤ (N+1)/L := Nat.div_le_div_right ((he k hk).trans (Nat.le_succ N))
    have hu : j∈U := by
      rcases hj.eq_or_lt with h₁ | h₁
      · exact mem_insert.mpr (Or.inl h₁)
      · exact mem_insert.mpr (Or.inr (mem_filter.mpr ⟨mem_range.mpr h₁,
          same_block hcell (hh k hk (le_of_not_gt h))⟩))
    exact mem_union_right _ (mem_biUnion.mpr ⟨j,hu,hcell⟩)
  have hc := card_biUnion_le_card_mul U cell L (fun j _ => by simp [cell,Nat.add_mul])
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  rw [card_range]
  exact Nat.add_le_add (Nat.le_refl J) (hc.trans (Nat.mul_le_mul_right L (card_insert_le _ _)))

/-- More than B(N+1)^d full disjoint signed blocks of length ceil((N+1)^a)
survive every large cutoff, for a < Θ and d < 1−a. All entries in a block
exceed A(N+1)^a in modulus, with the same sign. -/
theorem many_contiguous_mertens_excursions {a d : ℝ} (ha : 0 < a) (hθ : a < zetaZeroAbscissa)
    (hd : d < 1-a) (A B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B*((N:ℝ)+1)^d < ((signedMertensBlocks ⌈((N:ℝ)+1)^a⌉₊ N (A*((N:ℝ)+1)^a)).card:ℝ) := by
  obtain ⟨t,hat,ht⟩ := exists_between hθ
  have ht₀ := ha.trans hat
  obtain ⟨e,he,he1⟩ := exists_between ((div_lt_one ht₀).mpr hat)
  have het : a < e*t := (div_lt_iff₀ ht₀).mp he
  let v := max e (max (a+d) a)
  have hv : v < 1 := max_lt he1 (max_lt (by linarith only [hd]) (hθ.trans_le zetaZeroAbscissa_le_one))
  filter_upwards [all_cutoffs_many_mertens_excursions ht hv (|A|+2) (5+2*|B|)] with N hpop
  let X := (N:ℝ)+1
  have hX : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
  have xp := zero_lt_one.trans_le hX
  let L := ⌈X^a⌉₊
  let J := ⌈X^e⌉₊
  have hL : 0 < L := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos xp _)
  have hLmax : (L:ℝ) ≤ 2*X^a := by
    have ht := (Nat.ceil_lt_add_one (Real.rpow_nonneg xp.le a)).le
    linarith only [ht,Real.one_le_rpow hX ha.le]
  have hJ : (J:ℝ) ≤ 2*X^v := by
    have ht := (Nat.ceil_lt_add_one (Real.rpow_nonneg xp.le e)).le
    have hv0 : 0 ≤ v := ha.le.trans ((le_max_right (a+d) a).trans (le_max_right e _))
    linarith only [ht,Real.rpow_le_rpow_of_exponent_le hX (le_max_left e (max (a+d) a)),Real.one_le_rpow hX hv0]
  let E := mertensExcursions t (|A|+2) N
  have hcount := mertens_excursion_block_count (E:=E) (N:=N) (J:=J) (H:=A*X^a) hL
    (fun k hk => Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hk).1)) (fun k hk hlate => by
      have hg := (mem_filter.mp hk).2
      change (|A|+2)*((k:ℝ)+1)^t < _ at hg
      have hk' : X^e ≤ (k:ℝ)+1 := (Nat.le_ceil _).trans
        ((Nat.cast_le.mpr hlate).trans (by linarith))
      have hp := Real.rpow_le_rpow (Real.rpow_nonneg xp.le e) hk' ht₀.le
      rw [←Real.rpow_mul xp.le] at hp
      have hpow := (Real.rpow_le_rpow_of_exponent_le hX het.le).trans hp
      have hmul := mul_le_mul_of_nonneg_left hpow (show 0 ≤ |A|+2 by positivity)
      have hAmp := mul_le_mul_of_nonneg_right (le_abs_self A) (Real.rpow_nonneg xp.le a)
      linarith only [hAmp,hLmax,hmul,hg])
  by_contra! hsmall
  let G := signedMertensBlocks L N (A*X^a)
  change (G.card:ℝ) ≤ B*X^d at hsmall
  have hbound : (G.card:ℝ) ≤ |B| * X^d :=
    hsmall.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (Real.rpow_nonneg xp.le d))
  have hc : (E.card:ℝ) ≤ (J:ℝ)+((G.card:ℝ)+1)*(L:ℝ) := by exact_mod_cast hcount
  have hm := mul_le_mul (add_le_add hbound (le_refl (1:ℝ))) hLmax (Nat.cast_nonneg L) (by positivity)
  have hx : (|B| * X^d+1)*(2*X^a)=2*|B| * X^(a+d)+2*X^a := by rw [Real.rpow_add xp]; ring
  rw [hx] at hm
  have had := Real.rpow_le_rpow_of_exponent_le hX ((le_max_left (a+d) a).trans (le_max_right e _))
  have hav := Real.rpow_le_rpow_of_exponent_le hX ((le_max_right (a+d) a).trans (le_max_right e _))
  have hscaled := mul_le_mul_of_nonneg_left had (show 0 ≤ 2*|B| by positivity)
  change (5+2*|B|)*X^v < (E.card:ℝ) at hpop
  linarith only [hpop,hc,hJ,hm,hscaled,hav,Real.rpow_pos_of_pos xp v]

/-- Ordinary counting exponent for the largest possible thickness at a
strictly subcritical amplitude. Disjointness gives the matching upper bound. -/
theorem contiguous_mertens_counting_order {a : ℝ} (ha : 0 < a) (hθ : a < zetaZeroAbscissa) (A : ℝ) :
    let C := fun N : ℕ => ((signedMertensBlocks ⌈((N:ℝ)+1)^a⌉₊ N (A*((N:ℝ)+1)^a)).card:ℝ)
    Tendsto (fun N => Real.log (1+C N)/Real.log ((N:ℝ)+1)) atTop (𝓝 (1-a)) := by
  intro C
  have ha1 := hθ.trans_le zetaZeroAbscissa_le_one
  refine log_order_of_power_envelope (sub_pos.mpr ha1) (fun _ => Nat.cast_nonneg _) ?_ ?_
  · intro b _ hb
    simpa only [one_mul] using many_contiguous_mertens_excursions ha hθ hb A 1
  · intro c hc
    refine ⟨1,zero_le_one,fun N => ?_⟩
    let X := (N:ℝ)+1
    have hX : 1 ≤ X := le_add_of_nonneg_left (Nat.cast_nonneg N)
    have xp := zero_lt_one.trans_le hX
    let L := ⌈X^a⌉₊
    have hL := Nat.le_ceil (X^a)
    have hh : (C N)*L ≤ X := by
      have hb := card_le_card (filter_subset (fun j => _) (range ((N+1)/L)))
      change (signedMertensBlocks L N (A*X^a)).card ≤ _ at hb
      rw [card_range] at hb
      exact_mod_cast (Nat.mul_le_mul_right L hb).trans (Nat.div_mul_le_self (N+1) L)
    have hq : (C N) ≤ X^(1-a) := by
      rw [Real.rpow_sub xp,Real.rpow_one]
      exact (le_div_iff₀ (Real.rpow_pos_of_pos xp a)).mpr
        ((mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)).trans hh)
    simpa only [one_mul] using hq.trans (Real.rpow_le_rpow_of_exponent_le hX hc.le)

/-- Above Θ even the first member of a sufficiently late aligned block
cannot attain the threshold. -/
theorem supercritical_mertens_blocks_empty {a : ℝ} (ha : zetaZeroAbscissa < a) :
    ∀ᶠ N : ℕ in atTop, signedMertensBlocks ⌈((N:ℝ)+1)^a⌉₊ N (((N:ℝ)+1)^a)=∅ := by
  obtain ⟨t,ht,hta⟩ := exists_between ha
  have ht₀ := (by norm_num : (0:ℝ) ≤ 1/2).trans (half_le_zetaZeroAbscissa.trans ht.le)
  obtain ⟨B,hB,hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa (t-zetaZeroAbscissa) (sub_pos.mpr ht)
  rw [show zetaZeroAbscissa+(t-zetaZeroAbscissa)=t by ring] at hM
  have hx : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hta)).comp hx).eventually_gt_atTop B] with N hbig
  let X := (N:ℝ)+1
  have xp : 0 < X := by dsimp only [X]; positivity
  let L := ⌈X^a⌉₊
  have hL : 0 < L := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos xp a)
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hjr,hsign⟩ := mem_filter.mp hj
  have hjq : j+1 ≤ (N+1)/L := mem_range.mp hjr
  have hfull := (Nat.mul_le_mul_right L hjq).trans (Nat.div_mul_le_self (N+1) L)
  rw [Nat.add_mul,one_mul] at hfull
  have hk : j*L ≤ N := by omega
  have hmem : j*L∈Ico (j*L) ((j+1)*L) := mem_Ico.mpr ⟨le_rfl,by rw [Nat.add_mul,one_mul]; omega⟩
  have hlarge : X^a < |shiftedMertensReal (j*L)| := by
    rcases hsign with hpos | hneg
    · exact (hpos _ hmem).trans_le (le_abs_self _)
    · exact (by linarith only [hneg _ hmem] : X^a < -shiftedMertensReal (j*L)).trans_le (neg_le_abs _)
  rw [←norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal] at hlarge
  have hbnd := (hM (j*L)).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (add_le_add (Nat.cast_le.mpr hk) (le_refl (1:ℝ))) ht₀) hB)
  have hlt := mul_lt_mul_of_pos_right hbig (Real.rpow_pos_of_pos xp t)
  change B*X^t < X^(a-t)*X^t at hlt
  rw [← Real.rpow_add xp,sub_add_cancel] at hlt
  exact (hlarge.trans_le hbnd).not_ge hlt.le

/-- Disappearance of full one-sign blocks at every scale above b
characterizes the zero-free half-plane Re(s)>b. -/
theorem zero_abscissa_iff_eventual_absence_of_mertens_blocks {b : ℝ} (hb : 0 ≤ b) :
    zetaZeroAbscissa ≤ b ↔ ∀ a>b, ∀ᶠ N : ℕ in atTop,
      signedMertensBlocks ⌈((N:ℝ)+1)^a⌉₊ N (((N:ℝ)+1)^a)=∅ := by
  constructor
  · exact fun h a ha => supercritical_mertens_blocks_empty (h.trans_lt ha)
  · intro h
    by_contra! hbad
    obtain ⟨a,ha,hθ⟩ := exists_between hbad
    have ha1 := hθ.trans_le zetaZeroAbscissa_le_one
    have hpop := many_contiguous_mertens_excursions (hb.trans_lt ha) hθ (sub_pos.mpr ha1) 1 1
    obtain ⟨N,hN,hE⟩ := (hpop.and (h a ha)).exists
    simpa only [one_mul,hE,card_empty,Nat.cast_zero,Real.rpow_zero,not_lt_of_ge zero_le_one] using hN

#print axioms supercritical_mertens_blocks_empty
#print axioms zero_abscissa_iff_eventual_absence_of_mertens_blocks

#print axioms mertens_excursion_block_count
#print axioms many_contiguous_mertens_excursions
#print axioms contiguous_mertens_counting_order
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
