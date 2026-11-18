import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedBoundaryOfAPrefix
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary

/-!
# Signed surplus above the cube-root threshold

Every composite rough tail above this threshold has exactly two prime factors.
The pair count fits in nine tenths of the prime row, uniformly in both sharp
endpoints at fixed logarithmic relative width. Its divisor sum therefore has
a definite sign even when the least-prime cutoff varies with the interval.
-/

noncomputable section

open Finset Filter RHTower ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The single-prime exits of a least-prime row. -/
def tailPrimes (L U y : ℕ) := (Nat.primesLE U).filter (fun p => max L y < p)

/-- Composite squarefree tails whose prime factors all exceed the cutoff. -/
def compositeTails (L U y : ℕ) := (roughTails L U y).filter (fun n => ¬n.Prime)

private theorem peel_composite {L U y n : ℕ} (hn : n ∈ roughTails L U y) (hc : ¬n.Prime) :
    ∃ m ∈ roughTails (L/n.minFac) (U/n.minFac) n.minFac, m*n.minFac = n := by
  obtain ⟨hn1,_,hU,_,hy⟩ := mem_roughTails.mp hn
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hF : n ∈ (roughTails L U y).filter (fun w => w.minFac = n.minFac) :=
    mem_filter.mpr ⟨hn,rfl⟩
  rw [roughTails_minFac_fibre hp hy ((Nat.minFac_le (by omega)).trans hU)] at hF
  rcases mem_union.mp hF with h | h
  · split_ifs at h
    · exact False.elim (hc ((mem_singleton.mp h) ▸ hp))
    · exact False.elim (notMem_empty _ h)
  · exact mem_image.mp h

private theorem prime_of_short_tail {L U y n : ℕ} (hn : n ∈ roughTails L U y)
    (hs : n ≤ y^2) : n.Prime := by
  by_contra hc
  obtain ⟨m,hm,he⟩ := peel_composite hn hc
  obtain ⟨hm1,_,_,_,hp⟩ := mem_roughTails.mp hm
  obtain ⟨hn1,_,_,_,hy⟩ := mem_roughTails.mp hn
  have hp0 := (Nat.minFac_prime (by omega : n ≠ 1)).pos
  have hm' := hp.trans_le (Nat.minFac_le (by omega))
  have h := (Nat.mul_le_mul hy.le hy.le).trans_lt (Nat.mul_lt_mul_of_pos_right hm' hp0)
  rw [he,← pow_two] at h
  omega

/-- Every composite in a cube-root rough row has a unique least prime and a
larger prime as complementary factor. -/
theorem cube_root_tail_pair {L U y n : ℕ} (hU : U ≤ y^3) (hn : n ∈ compositeTails L U y) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ y < q ∧ q < r ∧ n = q*r := by
  obtain ⟨hn,hc⟩ := mem_filter.mp hn
  obtain ⟨hn1,_,hnu,_,hy⟩ := mem_roughTails.mp hn
  obtain ⟨m,hm,he⟩ := peel_composite hn hc
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hs : m ≤ n.minFac^2 := by
    by_contra! h
    have hh := Nat.mul_lt_mul_of_pos_right h hp.pos
    rw [he,← pow_succ] at hh
    exact (not_lt_of_ge (hnu.trans (hU.trans (Nat.pow_le_pow_left hy.le 3)))) hh
  have hpr := prime_of_short_tail hm hs
  obtain ⟨_,_,_,_,hlt⟩ := mem_roughTails.mp hm
  exact ⟨n.minFac,m,hp,hpr,hy,hpr.minFac_eq ▸ hlt,he.symm.trans (Nat.mul_comm m n.minFac)⟩

private theorem mem_tailPrimes {L U y p : ℕ} :
    p ∈ tailPrimes L U y ↔ p ∈ roughTails L U y ∧ p.Prime := by
  constructor
  · intro h
    obtain ⟨hP,hh⟩ := mem_filter.mp h
    obtain ⟨hpU,hp⟩ := Nat.mem_primesLE.mp hP
    obtain ⟨hL,hy⟩ := max_lt_iff.mp hh
    exact ⟨mem_roughTails.mpr ⟨hp.one_lt,hL,hpU,Irreducible.squarefree hp,
      hp.minFac_eq ▸ hy⟩,hp⟩
  · rintro ⟨hn,hp⟩
    obtain ⟨_,hL,hU,_,hy⟩ := mem_roughTails.mp hn
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hU,hp⟩,max_lt hL (hp.minFac_eq ▸ hy)⟩

/-- Exact signed residual after charging one prime for each composite tail. -/
theorem cube_root_tail_balance (L U y : ℕ) (hU : U ≤ y^3) :
    tailBalance L U y = ((tailPrimes L U y).card:ℤ) - (compositeTails L U y).card := by
  let P := tailPrimes L U y
  let C := compositeTails L U y
  have hsplit : roughTails L U y = P ∪ C := by
    ext n
    constructor
    · intro h
      by_cases hp : n.Prime
      · exact mem_union_left _ (mem_tailPrimes.mpr ⟨h,hp⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨h,hp⟩)
    · exact fun h => (mem_union.mp h).elim (fun a => (mem_tailPrimes.mp a).1)
        (fun a => (mem_filter.mp a).1)
  have hdis : Disjoint P C := disjoint_left.mpr (fun _ hP hC =>
    (mem_filter.mp hC).2 (mem_tailPrimes.mp hP).2)
  have hp : ∑ n ∈ P, μ n = -(P.card:ℤ) := by
    calc _ = ∑ _ ∈ P, (-1:ℤ) := sum_congr rfl (fun _ h => moebius_apply_prime (mem_tailPrimes.mp h).2)
         _ = _ := by simp
  have hc : ∑ n ∈ C, μ n = (C.card:ℤ) := by
    calc _ = ∑ _ ∈ C, (1:ℤ) := by
              apply sum_congr rfl
              intro n hn
              obtain ⟨q,r,hq,hr,_,hqr,rfl⟩ := cube_root_tail_pair hU hn
              rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.coprime_primes hq hr).2 hqr.ne),
                moebius_apply_prime hq,moebius_apply_prime hr]
              decide
         _ = _ := by simp
  change -(∑ n ∈ roughTails L U y, μ n) = (P.card:ℤ) - C.card
  rw [hsplit,sum_union hdis,hp,hc]
  ring

/-- Uniform positive signed balance on every sufficiently large cube-root
rough row of fixed logarithmic relative width. -/
theorem eventually_cube_root_signed_surplus (B : ℕ) :
    ∀ᶠ s : ℝ in atTop, ∀ L U y : ℕ, s^6 ≤ L → L ≤ U → (U:ℝ) ≤ 2*s^6 →
      s^6 / Real.log s ^ B ≤ (U:ℝ)-L → U ≤ y^3 →
      ((tailPrimes L U y).card:ℤ) ≤ 10 * tailBalance L U y := by
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_cubeProducts_nine_tenths B] with s hs hcap
  intro L U y hL hLU hU hw hy
  have hs0 : 0 ≤ s := by linarith only [hs]
  rw [cube_root_tail_balance L U y hy]
  by_cases hC : (compositeTails L U y).Nonempty
  · obtain ⟨n,hn⟩ := hC
    obtain ⟨q,r,_,hr,hyq,_,hen⟩ := cube_root_tail_pair hy hn
    have hnU := (mem_roughTails.mp (mem_filter.mp hn).1).2.2.1
    have hUL : U ≤ 2*L := by exact_mod_cast hU.trans (mul_le_mul_of_nonneg_left hL (by norm_num))
    have hqL : q ≤ L := by
      have ht := Nat.mul_le_mul_left q hr.two_le
      rw [hen] at hnU
      omega
    have hpEq : tailPrimes L U y = windowPrimes L U := by
      ext p
      rw [mem_windowPrimes (by positivity) (by positivity)]
      simp only [tailPrimes,mem_filter,Nat.mem_primesLE,max_eq_left (hyq.le.trans hqL),
        Nat.cast_lt,Nat.cast_le]
      tauto
    have hbase : s^2 ≤ (y:ℝ) := by
      apply (pow_le_pow_iff_left₀ (sq_nonneg s) (Nat.cast_nonneg _) (by decide : 3 ≠ 0)).1
      calc (s^2)^3 = s^6 := by ring
           _ ≤ (U:ℝ) := hL.trans (by exact_mod_cast hLU)
           _ ≤ _ := by exact_mod_cast hy
    have hsub : compositeTails L U y ⊆ cubeProducts s L U := by
      intro n hn
      obtain ⟨a,b,ha,hb,hya,hab,he⟩ := cube_root_tail_pair hy hn
      obtain ⟨_,hlo,hhi,_,_⟩ := mem_roughTails.mp (mem_filter.mp hn).1
      have ha0 : (0:ℝ)<a := by exact_mod_cast ha.pos
      rw [he] at hlo hhi ⊢
      have hprod : (a:ℝ)*b ≤ 2*s^6 := (by exact_mod_cast hhi : (a:ℝ)*b ≤ U).trans hU
      have hau : (a:ℝ) ≤ 2*s^3 := by
        by_contra! h
        have hv := mul_lt_mul_of_pos_right h (show 0 < (a:ℝ)+2*s^3 by positivity)
        have hsq := mul_le_mul_of_nonneg_left (by exact_mod_cast hab.le : (a:ℝ) ≤ b) ha0.le
        nlinarith only [hsq,hv,hprod,pow_nonneg hs0 6]
      refine mem_biUnion.mpr ⟨a,(mem_windowPrimes (by positivity) (by positivity)).2
        ⟨ha,?_,hau⟩,mem_image.mpr ⟨b,(mem_windowPrimes (by positivity) (by positivity)).2
        ⟨hb,?_,?_⟩,rfl⟩⟩
      · have hlay : (y:ℝ)<a := by exact_mod_cast hya
        linarith only [hbase,hlay,sq_nonneg s]
      · rw [div_lt_iff₀ ha0,mul_comm]; exact_mod_cast hlo
      · rw [le_div_iff₀ ha0,mul_comm]; exact_mod_cast hhi
    have h := (Nat.mul_le_mul_left 10 (card_le_card hsub)).trans
      (hcap L U hL (by exact_mod_cast hLU) hU hw)
    rw [← hpEq] at h
    omega
  · rw [not_nonempty_iff_eq_empty.mp hC,card_empty,Nat.cast_zero,sub_zero]
    omega

end GaloisForLFunctions.RestrictedFactorizationCalculus
