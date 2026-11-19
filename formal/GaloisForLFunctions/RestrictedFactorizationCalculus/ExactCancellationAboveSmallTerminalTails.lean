import GaloisForLFunctions.RestrictedFactorizationCalculus.TheBooleanFibresAboveARoughTail
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet

/-!
# Exact cancellation above small terminal tails

Remove a possible factor of two, then strip eligible least primes at the
log-square cutoff. Every odd integer with terminal tail r and its even
double lie below exp(K (1 + log(r+1)²)). On completing these pairs their
contribution to the sharp Möbius prefix is exactly zero.
-/

noncomputable section

open Finset Filter ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private def logHeight (r : ℕ) : ℝ := 1+(Real.log ((r:ℝ)+1))^2

/-- The odd integer m has a stopped tail at most Y. The integer before
the final stripping step and its free divisor specify its whole fibre. -/
def hasSmallOddTail (Y m : ℕ) : Prop :=
  ¬2 ∣ m ∧ Squarefree m ∧
    (((primorial (logSquareCutoff m)).Coprime m ∧ m ≤ Y) ∨
      ∃ p r c, TerminalPrimeTail logSquareCutoff p r ∧ c ∣ primorial (p-1) ∧
        r ≤ Y ∧ m=p*c*r)

private theorem logHeight_mono : Monotone logHeight := by
  intro m n h
  have hm : 1 ≤ (m:ℝ)+1 := by positivity
  exact add_le_add_left (pow_le_pow_left₀ (Real.log_nonneg hm)
    (Real.log_le_log (by positivity) (add_le_add_right (Nat.cast_le.mpr h) 1)) 2) 1

private theorem prime_above_tail_bound :
    ∃ C : ℝ,1 ≤ C ∧ ∀ p r,TerminalPrimeTail logSquareCutoff p r → (p:ℝ) ≤ C*logHeight r := by
  have he : ∀ᶠ x : ℝ in atTop,Real.log x ≤ (1/2:ℝ)*Real.sqrt x := by
    filter_upwards [(isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).bound
      (by norm_num : (0:ℝ)<1/2),eventually_ge_atTop (1:ℝ)] with x h hx
    rwa [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hx),
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _),←Real.sqrt_eq_rpow] at h
  obtain ⟨N,hN⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually he)
  let C := (N:ℝ)+4
  have hC : 4 ≤ C := by dsimp only [C]; linarith only [Nat.cast_nonneg N]
  refine ⟨C,by linarith only [hC],?_⟩
  intro p r tail
  let L := Real.log ((r:ℝ)+1)
  have hL : 0 ≤ L := Real.log_nonneg (by positivity)
  have hheight : 1 ≤ logHeight r := by dsimp only [logHeight]; linarith only [sq_nonneg L]
  by_cases big : N ≤ p
  · have small := hN p big
    have pp : 1 ≤ (p:ℝ) := by exact_mod_cast tail.prime.pos
    have hs : (p:ℝ) ≤ (⌊Real.log ((p:ℝ)*r+1)⌋₊:ℝ)^2 := by
      simpa only [logSquareCutoff,Nat.cast_mul,Nat.cast_pow] using (Nat.cast_le (α := ℝ)).mpr tail.removed
    have nonneg : 0 ≤ Real.log ((p:ℝ)*r+1) := Real.log_nonneg (by positivity)
    have hs' := hs.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le nonneg) 2)
    have root := (Real.sqrt_le_iff).2 ⟨nonneg,hs'⟩
    have room : (p:ℝ)*r+1 ≤ p*((r:ℝ)+1) := by linarith only [pp]
    have bound := Real.log_le_log (by positivity) room
    rw [Real.log_mul (by positivity) (by positivity)] at bound
    have h2 : Real.sqrt p ≤ 2*L := by linarith only [root,bound,small]
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rw [Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    have cap : (p:ℝ) ≤ 4*logHeight r := by change _ ≤ 4*(1+L^2); linarith only [hsq]
    exact cap.trans (mul_le_mul_of_nonneg_right hC (zero_le_one.trans hheight))
  · have hp : (p:ℝ) ≤ N := Nat.cast_le.mpr (le_of_not_ge big)
    have c0 := (by linarith only [hC] : 0 ≤ C)
    exact (hp.trans (by dsimp only [C]; linarith)).trans (le_mul_of_one_le_right c0 hheight)

/-- Uniform upper bound on the even double of every odd member with a
given upper bound for its terminal tail. -/
theorem diameter_of_small_terminal_tails :
    ∃ K : ℝ,0<K ∧ ∀ Y m,hasSmallOddTail Y m → Real.log (2*(m:ℝ)) ≤ K*logHeight Y := by
  obtain ⟨C,hC,hp⟩ := prime_above_tail_bound
  let K := 5*C+2
  have hK : 2 ≤ K := by dsimp only [K]; linarith only [hC]
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have log4 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
  have cap (r : ℕ) : Real.log r ≤ logHeight r := by
    by_cases h : r=0
    · simp [h,logHeight]
    have hh := Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) (by linarith : (r:ℝ) ≤ r+1)
    dsimp only [logHeight]; nlinarith only [hh,sq_nonneg (Real.log ((r:ℝ)+1)-1)]
  refine ⟨K,by linarith only [hK],?_⟩
  rintro Y m ⟨_,hs,hm⟩
  have mpos : (0:ℝ)< m := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs.ne_zero)
  rw [Real.log_mul (by norm_num) mpos.ne']
  rcases hm with ⟨_,hle⟩ | ⟨p,r,c,tail,hc,hry,rfl⟩
  · have h1 : 1 ≤ logHeight m := by unfold logHeight; linarith only [sq_nonneg (Real.log ((m:ℝ)+1))]
    have h2 : Real.log 2+Real.log m ≤ 2*logHeight m := by linarith only [log2,cap m,h1]
    exact h2.trans (mul_le_mul hK (logHeight_mono hle) (zero_le_one.trans h1) (by linarith only [hK]))
  · have hpp : (0:ℝ)<p := Nat.cast_pos.mpr tail.prime.pos
    have hcc : (0:ℝ)<c := Nat.cast_pos.mpr (Nat.pos_of_dvd_of_pos hc (primorial_pos _))
    have hrr : (0:ℝ)<r := Nat.cast_pos.mpr (Nat.pos_of_ne_zero tail.squarefree.ne_zero)
    have co : c ≤ 4^p := (Nat.le_of_dvd (primorial_pos _) hc).trans
      ((primorial_le_four_pow _).trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le p 1)))
    have lc := Real.log_le_log hcc (show (c:ℝ) ≤ (4:ℝ)^p by exact_mod_cast co)
    rw [Real.log_pow] at lc
    have lc' := mul_le_mul_of_nonneg_left log4 hpp.le
    have lp := Real.log_le_sub_one_of_pos hpp
    have h1 : 1 ≤ logHeight r := by unfold logHeight; linarith only [sq_nonneg (Real.log ((r:ℝ)+1))]
    push_cast
    rw [Real.log_mul (mul_pos hpp hcc).ne' hrr.ne',Real.log_mul hpp.ne' hcc.ne']
    apply le_trans _ (mul_le_mul_of_nonneg_left (logHeight_mono hry) (by linarith only [hK] : 0 ≤ K))
    dsimp only [K]
    linarith only [lc,lc',lp,hp p r tail,cap r,log2,h1,hpp]

/-- All odd members at the observation cutoff, together with the even
doubles that are present at that same cutoff. -/
def smallTerminalVertices (Y X : ℕ) : Finset ℕ := by
  classical
  exact ((Icc 1 X).filter (hasSmallOddTail Y)) ∪
    (((Icc 1 (X/2)).filter (hasSmallOddTail Y)).image (2*·))

/-- Beyond the explicit log-height threshold every small-tail pair is
complete. Its actual charge in the sharp Möbius prefix vanishes. -/
theorem exact_cancellation_above_small_terminal_tails :
    ∃ K : ℝ,0<K ∧ ∀ X Y : ℕ,0<X → K*(1+(Real.log ((Y:ℝ)+1))^2) ≤ Real.log X →
      ∑ n ∈ smallTerminalVertices Y X,(μ n:ℝ)=0 := by
  classical
  obtain ⟨K,hK,diam⟩ := diameter_of_small_terminal_tails
  refine ⟨K,hK,?_⟩
  intro X Y hX hroom
  let A := (Icc 1 X).filter (hasSmallOddTail Y)
  have same : (Icc 1 (X/2)).filter (hasSmallOddTail Y)=A := by
    ext m
    simp only [A,mem_filter,mem_Icc]
    constructor
    · rintro ⟨⟨hm,hh⟩,ht⟩; exact ⟨⟨hm,hh.trans (Nat.div_le_self ..)⟩,ht⟩
    · rintro ⟨⟨hm,_⟩,ht⟩
      have bound := (Real.log_le_log_iff (by positivity : (0:ℝ)<2*(m:ℝ)) (Nat.cast_pos.mpr hX)).1
        ((diam Y m ht).trans hroom)
      have hn : 2*m ≤ X := by exact_mod_cast bound
      exact ⟨⟨hm,(Nat.le_div_iff_mul_le (by decide : 0<2)).2 (by rwa [Nat.mul_comm])⟩,ht⟩
  have dis : Disjoint A (A.image (2*·)) := by
    apply disjoint_left.mpr
    intro n hn hdouble
    obtain ⟨m,_,rfl⟩ := mem_image.mp hdouble
    exact (mem_filter.mp hn).2.1 (dvd_mul_right ..)
  have inj : Set.InjOn (fun m : ℕ => 2*m) A := fun _ _ _ _ he =>
    Nat.eq_of_mul_eq_mul_left (by decide : 0<2) he
  have opp (m : ℕ) (hm : m ∈ A) : (μ (2*m):ℝ) = -(μ m:ℝ) := by
    rw [isMultiplicative_moebius.map_mul_of_coprime (Nat.prime_two.coprime_iff_not_dvd.mpr (mem_filter.mp hm).2.1),
      moebius_apply_prime Nat.prime_two]; push_cast; ring
  rw [smallTerminalVertices,same,sum_union dis,sum_image inj]
  change (∑ m ∈ A,(μ m:ℝ))+(∑ m ∈ A,(μ (2*m):ℝ))=0
  rw [sum_congr rfl opp,sum_neg_distrib,add_neg_cancel]

end GaloisForLFunctions.RestrictedFactorizationCalculus
