import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheExactFirstSquarefreeBandwidth
import GaloisForLFunctions.RHTower.Sieve.ElementaryHarmonicBounds
import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff

/-!
# A cube-root gap bound for consecutive squarefree pairs

Each small prime square costs its local density plus at most one endpoint.
For large square divisors the complementary cofactor is small. At a
fixed cofactor, consecutive square multiples are separated by at least
the cofactor times the square-root cutoff. The odd composite nine leaves
a strict margin below one half in the sum of the prime-square densities.
-/
noncomputable section
open Finset Filter
open scoped Classical Topology
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval

private abbrev bad (A H : ℕ) := (Ioc A (A+H)).filter (fun n => ¬Squarefree n)
private abbrev roots (A H D k : ℕ) := (Ioc D (A+H)).filter (fun d => k*d^2 ∈ Ioc A (A+H))

private theorem square_sieve_margin (D : ℕ) :
    ∑ p∈Nat.primesLE D, 1/(p:ℝ)^2 ≤ 1/2-1/81 := by
  let S := (Nat.primesLE D).erase 2
  have hn : 9 ∉ S := fun h => (by decide : ¬Nat.Prime 9) (Nat.mem_primesLE.mp (mem_erase.mp h).2).2
  have hodd : ∀ n∈insert 9 S, 3 ≤ n ∧ ¬2 ∣ n := by
    intro n hn
    rcases mem_insert.mp hn with rfl|h
    · decide
    obtain ⟨hne,hp⟩ := mem_erase.mp h
    have prime := (Nat.mem_primesLE.mp hp).2
    obtain h|h := prime.eq_two_or_odd
    · exact (hne h).elim
    · have bound := prime.two_le
      exact ⟨by omega,by omega⟩
  have h := _root_.RHTower.Sieve.sum_inv_sq_odd_le hodd
  rw [sum_insert hn] at h
  by_cases ht : 2 ∈ Nat.primesLE D
  · have split := sum_erase_add (Nat.primesLE D) (fun n : ℕ => 1/(n:ℝ)^2) ht
    change (∑ n∈S,1/(n:ℝ)^2)+_= _ at split
    norm_num at h split ⊢
    linarith only [h,split]
  · have he : S=Nat.primesLE D := erase_eq_of_notMem ht
    rw [←he]
    norm_num at h ⊢
    linarith only [h]

private theorem small_square_price (A H D : ℕ) :
    ((∑ p∈Nat.primesLE D, ((Ioc A (A+H)).filter (fun m => p^2 ∣ m)).card:ℕ):ℝ) ≤
      (H:ℝ)*(1/2-1/81)+(Nat.primesLE D).card := by
  have term (p : ℕ) (hp : p ∈ Nat.primesLE D) :
      (((Ioc A (A+H)).filter (fun m => p^2 ∣ m)).card:ℝ) ≤ H*(1/(p:ℝ)^2)+1 := by
    have h := _root_.RHTower.Sieve.abs_card_filter_dvd_Ioc_sub_lt (p^2) A (A+H)
      (pow_pos (Nat.mem_primesLE.mp hp).2.pos 2) (Nat.le_add_right A H)
    have h' := (abs_lt.mp h).2
    rw [Nat.cast_add,Nat.cast_pow,add_sub_cancel_left] at h'
    linarith only [h',show (H:ℝ)* (1/(p:ℝ)^2)=(H:ℝ)/(p:ℝ)^2 by ring]
  push_cast
  apply (sum_le_sum term).trans
  rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one]
  exact add_le_add (mul_le_mul_of_nonneg_left (square_sieve_margin D) (Nat.cast_nonneg _)) le_rfl

private theorem roots_per_cofactor {A H D k : ℕ} (hD : 0 < D) (hk : 0 < k) :
    (roots A H D k).card ≤ 1+H/(k*D) := by
  let S := roots A H D k
  by_cases hn : S.Nonempty
  · let d := S.min' hn
    obtain ⟨hd,hd'⟩ := mem_filter.mp (min'_mem S hn)
    have hdD : D ≤ d := (mem_Ioc.mp hd).1.le
    have hsubset : S ⊆ Icc d (d+H/(k*D)) := by
      intro e he
      have hde : d ≤ e := min'_le _ _ he
      obtain ⟨_,he'⟩ := mem_filter.mp he
      obtain ⟨f,hf⟩ := Nat.exists_eq_add_of_le hde
      have hl := (mem_Ioc.mp hd').1
      have hu := (mem_Ioc.mp he').2
      have gap : k*d^2+f*(k*D) ≤ k*e^2 := by
        rw [hf]
        have bound := Nat.mul_le_mul_right (k*f) hdD
        nlinarith only [bound,Nat.zero_le (k*d*f),Nat.zero_le (k*f^2)]
      have hf' := (Nat.le_div_iff_mul_le (Nat.mul_pos hk hD)).mpr (show f*(k*D) ≤ H by omega)
      exact mem_Icc.mpr ⟨hde,by omega⟩
    exact (card_le_card hsubset).trans_eq (by rw [Nat.card_Icc];omega)
  · change S.card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hn,card_empty]
    exact Nat.zero_le _

private theorem large_square_price (A H K : ℕ) {D : ℕ} (hD : 0 < D) :
    (∑ k∈Icc 1 K,(roots A H D k).card) ≤ K+(H/D)^2 := by
  let P := H/D
  have term (k : ℕ) (hk : k ∈ Icc 1 K) :
      (roots A H D k).card ≤ 1+(if k ≤ P then P else 0) := by
    have kp := (mem_Icc.mp hk).1
    apply (roots_per_cofactor hD kp).trans
    apply Nat.add_le_add_left
    split_ifs with h
    · apply Nat.div_le_div_left _ hD
      simpa using Nat.mul_le_mul_right D kp
    · have hlt := (Nat.div_lt_iff_lt_mul hD).mp (show H/D < k from lt_of_not_ge h)
      rw [Nat.div_eq_of_lt hlt]
  apply (sum_le_sum term).trans
  rw [sum_add_distrib,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one,←sum_filter]
  have hsub : ((Icc 1 K).filter (fun k => k ≤ P)) ⊆ Icc 1 P := by
    intro k hk
    exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hk).1).1,(mem_filter.mp hk).2⟩
  have hcard : ((Icc 1 K).filter (fun k => k ≤ P)).card ≤ P := by
    simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hsub
  simp only [sum_const,nsmul_eq_mul,pow_two]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right P hcard) K

/-- A finite interval bound for nonsquarefree integers, uniform in the
initial point, length and splitting divisor. -/
theorem nonsquarefree_count_on_a_short_interval (A H : ℕ) {D : ℕ} (hD : 0 < D) :
    (((Ioc A (A+H)).filter (fun n => ¬Squarefree n)).card:ℝ) ≤ H*(1/2-1/81:ℝ)+(Nat.primesLE D).card+((A+H)/D^2:ℕ)+((H/D:ℕ):ℝ)^2 := by
  let K := (A+H)/D^2
  let small := (Nat.primesLE D).biUnion (fun p => (Ioc A (A+H)).filter (fun m => p^2 ∣ m))
  let large := (Icc 1 K).biUnion (fun k => (roots A H D k).image (fun d => k*d^2))
  have cover : bad A H ⊆ small ∪ large := by
    intro n hn
    obtain ⟨hI,hbad⟩ := mem_filter.mp hn
    have pos := (Nat.zero_le A).trans_lt (mem_Ioc.mp hI).1
    obtain ⟨p,hp,hdiv⟩ : ∃ p : ℕ,p.Prime ∧ p*p ∣ n := by
      by_contra! h
      exact hbad (Nat.squarefree_iff_prime_squarefree.mpr h)
    rw [←pow_two] at hdiv
    by_cases hle : p ≤ D
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,Nat.mem_primesLE.mpr ⟨hle,hp⟩,mem_filter.mpr ⟨hI,hdiv⟩⟩)
    obtain ⟨k,he⟩ := hdiv
    have hk : 0 < k := by by_contra! h;have hz : k=0 := by omega;simp [hz] at he;omega
    have pk : k*D^2 ≤ n := by
      rw [he,mul_comm]
      exact Nat.mul_le_mul_left k (Nat.pow_le_pow_left (le_of_lt (lt_of_not_ge hle)) 2)
    have hK : k ≤ K := (Nat.le_div_iff_mul_le (pow_pos hD 2)).mpr (pk.trans (mem_Ioc.mp hI).2)
    have hpn : p ≤ n := (Nat.le_self_pow (by decide : 2≠0) p).trans (Nat.le_of_dvd pos ⟨k,he⟩)
    have eq : k*p^2=n := (Nat.mul_comm ..).trans he.symm
    exact mem_union_right _ (mem_biUnion.mpr ⟨k,mem_Icc.mpr ⟨hk,hK⟩,mem_image.mpr
      ⟨p,mem_filter.mpr ⟨mem_Ioc.mpr ⟨lt_of_not_ge hle,hpn.trans (mem_Ioc.mp hI).2⟩,eq.symm ▸ hI⟩,eq⟩⟩)
  have hs := card_biUnion_le (s:=Nat.primesLE D) (t:=fun p => (Ioc A (A+H)).filter (fun m => p^2 ∣ m))
  have hl := (card_biUnion_le (s:=Icc 1 K) (t:=fun k => (roots A H D k).image (fun d => k*d^2))).trans
    ((sum_le_sum (fun k _ => card_image_le (s:=roots A H D k))).trans (large_square_price A H K hD))
  have bound := (card_le_card cover).trans (card_union_le _ _)
  have counts := bound.trans (Nat.add_le_add hs hl)
  have hh := (Nat.cast_le (α:=ℝ)).mpr counts
  push_cast at hh
  have smallBound := small_square_price A H D
  push_cast at smallBound
  change _ ≤ _+(K:ℝ)+_
  linarith only [hh,smallBound]

private theorem covering_pairless_block {A H : ℕ}
    (missing : ∀ n ∈ Ioc A (A+H), ¬(Squarefree n ∧ Squarefree (n+1))) :
    H ≤ (bad A H).card+(bad (A+1) H).card := by
  let f := fun n : ℕ => if Squarefree n then Sum.inr (n+1) else Sum.inl n
  have hcard : (Ioc A (A+H)).card ≤ ((bad A H).disjSum (bad (A+1) H)).card := by
    apply card_le_card_of_injOn f
    · intro n hn
      dsimp only [f]
      split_ifs with hs
      · apply inr_mem_disjSum.mpr
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (mem_Ioc.mp hn).1;omega,
          by have := (mem_Ioc.mp hn).2;omega⟩,fun h => missing n hn ⟨hs,h⟩⟩
      · exact inl_mem_disjSum.mpr (mem_filter.mpr ⟨hn,hs⟩)
    · intro m _ n _ he
      dsimp only [f] at he
      split_ifs at he <;> simp_all
  simpa only [Nat.card_Ioc,Nat.add_sub_cancel_left,card_disjSum] using hcard

/-- A missing pair forces a price in endpoint errors at small primes and
in the number of large-square cofactors. -/
theorem local_price_of_a_squarefree_pair_gap {A H D : ℕ} (hD : 0 < D)
    (missing : ∀ n ∈ Ioc A (A+H), ¬(Squarefree n ∧ Squarefree (n+1))) :
    (H:ℝ)/81 ≤ (Nat.primesLE D).card+((A+H+1)/D^2:ℕ)+((H/D:ℕ):ℝ)^2 := by
  have hcover : (H:ℝ) ≤ ((bad A H).card:ℝ)+((bad (A+1) H).card:ℝ) := by
    exact_mod_cast covering_pairless_block missing
  have hleft := nonsquarefree_count_on_a_short_interval A H hD
  have hright := nonsquarefree_count_on_a_short_interval (A+1) H hD
  rw [show A+1+H=A+H+1 by omega] at hright
  have hdiv : (((A+H)/D^2:ℕ):ℝ) ≤ (((A+H+1)/D^2:ℕ):ℝ) :=
    Nat.cast_le.mpr (Nat.div_le_div_right (Nat.le_succ _))
  linarith only [hcover,hleft,hright,hdiv]

private theorem price_at_last {N H D : ℕ} (hN : 2 ≤ N) (hD : 0 < D)
    (hage : H+1 < N-lastSquarefreeNeighbor N) :
    (H:ℝ)/81 ≤ (Nat.primesLE D).card+(N/D^2:ℕ)+((H/D:ℕ):ℝ)^2 := by
  let A := N-H-1
  have hlt : lastSquarefreeNeighbor N < A := by dsimp only [A];omega
  have hcut : A+H+1=N := by dsimp only [A];omega
  have price := local_price_of_a_squarefree_pair_gap (A:=A) (H:=H) hD (by
    intro n hn hpair
    have lo := (mem_Ioc.mp hn).1
    have up := (mem_Ioc.mp hn).2
    have hm := (last_squarefree_neighbor_spec hN).2.2.2.2 n
      ((Nat.zero_le A).trans_lt lo) (by omega) hpair.1 hpair.2
    omega)
  simpa only [hcut] using price

/-- A sieve cutoff whose endpoint error fits below the cutoff gives a
finite bound for the distance to the last adjacent squarefree pair. -/
theorem last_pair_age_from_prime_count {N D : ℕ} (hN : 2 ≤ N)
    (fits : 81 * ((Nat.primesLE D).card + N / D^2) + 1 < D) :
    N - lastSquarefreeNeighbor N ≤ 81 * ((Nat.primesLE D).card + N / D^2) + 2 := by
  let E := (Nat.primesLE D).card + N / D^2
  let H := 81 * E + 1
  have hd : H < D := fits
  by_contra! gap
  have hg : H + 1 < N - lastSquarefreeNeighbor N := gap
  have price := price_at_last hN ((Nat.zero_le H).trans_lt hd) hg
  rw [Nat.div_eq_of_lt hd, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at price
  have he : (E : ℝ) = ((Nat.primesLE D).card : ℝ) + (N / D^2 : ℕ) := Nat.cast_add ..
  have hh : (H : ℝ) = 81 * (E : ℝ) + 1 := by simp only [H, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith only [price, he, hh]

private theorem cube_root_cubed {x : ℝ} (hx : 0 ≤ x) :
    (x^(1/3:ℝ))^3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

private theorem cube_root_squared {x : ℝ} (hx : 0 ≤ x) :
    (x^(1/3:ℝ))^2 = x^(2/3:ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- Balancing the count of small primes against the number of large-square
cofactors saves two thirds of a logarithm over the cube-root scale. -/
theorem last_squarefree_pair_logarithmic_cube_root_bound :
    ∀ᶠ N : ℕ in atTop, ((N - lastSquarefreeNeighbor N : ℕ) : ℝ) ≤
      1055 * (N : ℝ)^(1/3:ℝ) / (Real.log N)^(2/3:ℝ) := by
  let r := fun N : ℕ => (N:ℝ)^(1/3:ℝ)
  let t := fun N : ℕ => (Real.log N)^(1/3:ℝ)
  let D := fun N : ℕ => ⌈r N * t N⌉₊
  have grow := tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/3)
  have natGrow := tendsto_natCast_atTop_atTop (R:=ℝ)
  have logGrow := Real.tendsto_log_atTop.comp natGrow
  have rootGrow : Tendsto r atTop atTop := grow.comp natGrow
  have tGrow : Tendsto t atTop atTop := grow.comp logGrow
  have dGrow : Tendsto D atTop atTop :=
    tendsto_nat_ceil_atTop.comp (rootGrow.atTop_mul_atTop₀ tGrow)
  have pnt := _root_.RHTower.tendsto_primeCounting_nat_ratio.comp dGrow
  have small := (Real.tendsto_pow_log_div_pow_atTop (1/3) (2/3) (by norm_num)).comp natGrow
  filter_upwards [eventually_ge_atTop 2, logGrow.eventually_ge_atTop 1100,
    rootGrow.eventually_ge_atTop 1, tGrow.eventually_ge_atTop 1,
    pnt.eventually_lt_const (by norm_num : (1:ℝ) < 2),
    small.eventually_lt_const (by norm_num : (0:ℝ) < 1)] with N hN hlog hr ht hp hs
  let A := r N / (t N)^2
  have hx : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  have logpos : 0 < Real.log N := by change 1100 ≤ Real.log (N:ℝ) at hlog; linarith only [hlog]
  have rp : 0 < r N := zero_lt_one.trans_le hr
  have tp : 0 < t N := zero_lt_one.trans_le ht
  have t3 : (t N)^3 = Real.log N := cube_root_cubed logpos.le
  have t2 : (t N)^2 = (Real.log N)^(2/3:ℝ) := cube_root_squared logpos.le
  have r3 : (r N)^3 = (N:ℝ) := cube_root_cubed hx.le
  have hA : 1 ≤ A := by
    apply (le_div_iff₀ (sq_pos_of_pos tp)).mpr
    change (Real.log N)^(2/3:ℝ) / r N < 1 at hs
    rw [← t2] at hs
    simpa only [one_mul] using ((div_lt_iff₀ rp).mp hs).le
  have ar : A * Real.log N = r N * t N := by
    dsimp only [A]; rw [← t3]; field_simp [tp.ne'] <;> ring
  have dl : r N * t N ≤ (D N:ℝ) := Nat.le_ceil _
  have low := one_le_mul_of_one_le_of_one_le hr ht
  have du : (D N:ℝ) ≤ 2*(r N*t N) := by
    have un := Nat.ceil_lt_add_one (mul_nonneg rp.le tp.le)
    change ((⌈r N * t N⌉₊ : ℕ) : ℝ) ≤ _
    linarith only [un, low]
  have ld := Real.log_le_log rp ((le_mul_of_one_le_right rp.le ht).trans dl)
  change Real.log ((N:ℝ)^(1/3:ℝ)) ≤ Real.log (D N) at ld
  rw [Real.log_rpow hx] at ld
  have ldp : 0 < Real.log (D N) := (mul_pos (by norm_num : (0:ℝ) < 1/3) logpos).trans_le ld
  let pi := ((Nat.primesLE (D N)).card:ℝ)
  have pip : 0 ≤ pi := Nat.cast_nonneg _
  have dp : 0 < (D N:ℝ) := (mul_pos rp tp).trans_le dl
  have ppaid : pi * Real.log (D N) ≤ 2*(D N:ℝ) := by
    change (Nat.primeCounting (D N):ℝ)/((D N:ℝ)/Real.log (D N)) < 2 at hp
    have h := ((div_lt_iff₀ (div_pos dp ldp)).mp hp).le
    dsimp only [pi]; rw [Nat.primesLE_card_eq_primeCounting, ← le_div_iff₀ ldp]
    simpa only [mul_div_assoc] using h
  have piBound : pi ≤ 12*A := by
    apply (mul_le_mul_iff_left₀ logpos).mp
    have h := mul_le_mul_of_nonneg_left ld pip
    rw [mul_assoc, ar]
    linarith only [h, ppaid, du]
  have cof : (((N/(D N)^2:ℕ):ℝ)) ≤ A := by
    have floor := (Nat.cast_le (α:=ℝ)).mpr (Nat.div_mul_le_self N ((D N)^2))
    push_cast at floor
    have paid := (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg rp.le tp.le) dl 2)
      (Nat.cast_nonneg (α:=ℝ) (N/(D N)^2))).trans floor
    have hh := (le_div_iff₀ (sq_pos_of_pos (mul_pos rp tp))).mpr paid
    rw [← r3] at hh
    exact hh.trans_eq (by dsimp only [A]; field_simp [rp.ne', tp.ne'] <;> ring)
  let E := (Nat.primesLE (D N)).card + N / (D N)^2
  have paid : (E:ℝ) ≤ 13*A := by
    dsimp only [E]; rw [Nat.cast_add]
    change pi + _ ≤ _
    linarith only [piBound, cof]
  have fits : 81 * E + 1 < D N := by
    have scale := mul_le_mul_of_nonneg_left (show 1100 ≤ Real.log N from hlog) (zero_le_one.trans hA)
    rw [ar] at scale
    have hh : 81*(E:ℝ)+1 < (D N:ℝ) := by linarith only [scale, dl, paid, hA]
    exact_mod_cast hh
  have age := (Nat.cast_le (α:=ℝ)).mpr (last_pair_age_from_prime_count hN fits)
  change ((N-lastSquarefreeNeighbor N:ℕ):ℝ) ≤ ((81*E+2:ℕ):ℝ) at age
  push_cast at age
  rw [← t2, mul_div_assoc]
  change _ ≤ 1055*A
  linarith only [age, paid, hA]

/-- The age is little-o of the cube root even along cutoffs inside
arbitrarily long runs without a squarefree pair. -/
theorem last_squarefree_pair_cube_root_saving :
    Tendsto (fun N : ℕ => ((N-lastSquarefreeNeighbor N:ℕ):ℝ)/(N:ℝ)^(1/3:ℝ)) atTop (𝓝 0) := by
  have l := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 2/3)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have h := l.inv_tendsto_atTop.const_mul (1055:ℝ)
  rw [mul_zero] at h
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_ h
  filter_upwards [last_squarefree_pair_logarithmic_cube_root_bound, eventually_ge_atTop 2] with N hN ht
  have hx : 0 < (N:ℝ) := Nat.cast_pos.mpr (by omega)
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hx _)).mpr
  exact hN.trans_eq (by change _ = 1055*((Real.log N)^(2/3:ℝ))⁻¹*((N:ℝ)^(1/3:ℝ)); ring)

end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
