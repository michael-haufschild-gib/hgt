import GaloisForLFunctions.CountingHolography.Sections.StabilizationOfPrimeValuationsInSquareProducts
import GaloisForLFunctions.CountingHolography.Sections.ThePrimeExponentsOnTheSquareDiagonal
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity

/-!
# Inner primes in the reduced numerator of square-generator prefixes

Each negative long lag at root j has its positive counterpart at root 2j+1.
After the support cutoff, injection leaves enough positive mass at each
large prime to dominate all the individual floors.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology Finset ArithmeticWeightTheory ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge AbsoluteGeometryOfSpecZ _root_.RHTower

private def bump (p j : ℕ) := splineAutoCorr (Real.log ((j:ℝ)^2)-Real.log p)
private def B (p j : ℕ) := (j:ℝ)^2*bump p j
private abbrev q (j : ℕ) := ordinaryPrimeGenerator (j • successorSquareTriple j)

private theorem B_nonneg (p j : ℕ) : 0 ≤ B p j := mul_nonneg (sq_nonneg _) (splineAutoCorr_nonneg _)

/-- The positive row at the odd successor outweighs the subtracted row
at the original root, up to the mesh and floor allowance. -/
private theorem row_lower : ∃ K : ℝ, 0 ≤ K ∧ ∀ {p j : ℕ}, p.Prime → 0 < j →
    8+Real.log 9 < Real.log p →
    (2/Real.sqrt p)*(2*B p j-B p (2*j+1))-K ≤ (deningerRatExp (q j) p:ℝ) := by
  obtain ⟨C,hC,hmesh⟩ := original_contact_quadrature
  refine ⟨C+1,by positivity,fun {p j} hp hj hlarge => ?_⟩
  let N := (2*j+1)^2+1
  let a := j • successorSquareTriple j
  let X := contactMultiplicity (packet a) (3*windowEnd N) (resolution a) p
  have hsq : (j:ℝ)^2 ≤ ((2*j+1:ℕ):ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _)
    (by exact_mod_cast (by omega : j ≤ 2*j+1)) 2
  have hE := ordinaryPrimeGenerator_exponent a p
  change deningerRatExp (q j) p=if p ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime then ⌊X⌋ else 0 at hE
  by_cases hs : p ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime
  · rw [if_pos hs] at hE
    have h₁ : |X-integratedContact a p| ≤ C := (hmesh N a hp.pos).trans (div_le_self hC (by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1:ℝ) ≤ p by exact_mod_cast hp.pos)))
    have h₂ : (2/Real.sqrt p)*(2*B p j-B p (2*j+1)) ≤ integratedContact a p := by
      rw [show a=j • successorSquareTriple j from rfl,integratedContact_nsmul,successorSquare_long_contact hj hlarge]
      have he := mul_le_mul_of_nonneg_right hsq (splineAutoCorr_nonneg
        (Real.log (((2*j+1:ℕ):ℝ)^2)-Real.log p))
      dsimp only [B,bump]
      calc _ ≤ (2/Real.sqrt p)*((j:ℝ)^2*(2*splineAutoCorr (Real.log ((j:ℝ)^2)-Real.log p)-
                splineAutoCorr (Real.log (((2*j+1:ℕ):ℝ)^2)-Real.log p))) :=
               mul_le_mul_of_nonneg_left (by linarith only [he]) (by positivity)
           _ = _ := by ring
    rw [hE]
    linarith only [(abs_le.mp h₁).1,h₂,Int.sub_one_lt_floor X]
  · rw [if_neg hs] at hE
    have hcut : 3*windowEnd N < p :=
      lt_of_not_ge fun h => hs (mem_filter.mpr ⟨mem_Icc.mpr ⟨hp.two_le,h⟩,hp⟩)
    have hfar : successorSquareWindowScale j < p := (successorSquareWindowScale_bounds j).2.2.trans_lt
      (by exact_mod_cast (by omega : windowEnd N < p))
    have hz {i : ℕ} (hi : 0 < i) (hi' : (i:ℝ)^2 ≤ ((2*j+1:ℕ):ℝ)^2) : bump p i=0 := by
      apply splineAutoCorr_zero_outside
      apply lt_abs.mpr
      right
      have h := Real.log_lt_log (mul_pos (Real.exp_pos 8) (sq_pos_of_pos (Nat.cast_pos.mpr hi)))
        ((mul_le_mul_of_nonneg_left hi' (Real.exp_pos _).le).trans_lt hfar)
      rw [Real.log_mul (Real.exp_pos _).ne' (sq_pos_of_pos (Nat.cast_pos.mpr hi)).ne',Real.log_exp] at h
      linarith only [h]
    simp only [B,hz hj hsq,hz (Nat.succ_pos (2*j)) le_rfl,mul_zero,sub_zero,hE,Int.cast_zero]
    linarith only [hC]

private theorem odd_sum_le {p M : ℕ} (hvan : ∀ j : ℕ, M < j → B p j=0) :
    ∑ j ∈ Ioc 0 M, B p (2*j+1) ≤ ∑ j ∈ Ioc 0 M, B p j := by
  let f := fun j : ℕ => 2*j+1
  let S := Ioc 0 M
  have hinj : Set.InjOn f (↑S) := fun i _ j _ h => by dsimp only [f] at h; omega
  change (∑ j ∈ S, B p (f j)) ≤ ∑ j ∈ S, B p j
  rw [← Finset.sum_image (f := B p) hinj]
  let U := Ioc 0 (2*M+1)
  have hsub : S.image f ⊆ U := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    have hj' := (mem_Ioc.mp hj).2
    exact mem_Ioc.mpr ⟨Nat.succ_pos _,by dsimp only [f]; omega⟩
  have hsub' : S ⊆ U := fun k hk => mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,(mem_Ioc.mp hk).2.trans (by omega)⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => B_nonneg p k)).trans_eq ?_
  exact (sum_subset hsub' (fun k hk h => hvan k (lt_of_not_ge fun hh =>
    h (mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,hh⟩)))).symm

/-- The central band of roots contributes a fixed positive multiple
of p for each of at least √p/2 roots. -/
private theorem central_bump_mass : ∃ c : ℝ, 0 < c ∧ ∀ {p M : ℕ}, 2 ≤ Real.sqrt p →
    2*Real.sqrt p ≤ M → c*p ≤ (2/Real.sqrt p)*∑ j ∈ Ioc 0 M, B p j := by
  have hl₄ := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hl₄)
    continuous_splineAutoCorr.continuousOn
  let c := splineAutoCorr u
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4)
  have hc : 0 < c := splineAutoCorr_interior (by
    rw [abs_of_nonneg hu.1]
    linarith only [hu.2,hl])
  refine ⟨c,hc,fun {p M} hp hM => ?_⟩
  let x := Real.sqrt p
  change 2 ≤ x at hp
  have hx : 0 < x := lt_of_lt_of_le two_pos hp
  have hpx : x^2=(p:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hp' : (0:ℝ) < p := (sq_pos_of_pos hx).trans_eq hpx
  let S := Ioc ⌊x⌋₊ ⌊2*x⌋₊
  have hsub : S ⊆ Ioc 0 M := by
    intro j hj
    obtain ⟨hl,hh⟩ := mem_Ioc.mp hj
    refine mem_Ioc.mpr ⟨(Nat.zero_le _).trans_lt hl,?_⟩
    exact Nat.cast_le.mp ((Nat.cast_le.mpr hh).trans ((Nat.floor_le (by positivity : 0 ≤ 2*x)).trans hM))
  have hcard : x/2 ≤ (S.card:ℝ) := by
    rw [show S=Ioc ⌊x⌋₊ ⌊2*x⌋₊ from rfl,Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono (by linarith only [hx] : x ≤ 2*x))]
    linarith only [Nat.floor_le hx.le,Nat.lt_floor_add_one (2*x),hp]
  have hterm (j : ℕ) (hj : j ∈ S) : c*p ≤ B p j := by
    obtain ⟨hl,hh⟩ := mem_Ioc.mp hj
    have hlo : x ≤ (j:ℝ) := (Nat.lt_floor_add_one x).le.trans
      (by exact_mod_cast (Nat.succ_le_of_lt hl))
    have hhi : (j:ℝ) ≤ 2*x := (Nat.cast_le.mpr hh).trans (Nat.floor_le (by positivity))
    have h₁ := pow_le_pow_left₀ hx.le hlo 2
    rw [hpx] at h₁
    have h₂ := pow_le_pow_left₀ (Nat.cast_nonneg j) hhi 2
    rw [mul_pow,hpx] at h₂
    have hlog : Real.log ((j:ℝ)^2)-Real.log p ∈ Set.Icc 0 (Real.log 4) := by
      rw [← Real.log_div (hp'.trans_le h₁).ne' hp'.ne']
      exact ⟨Real.log_nonneg ((one_le_div hp').mpr h₁),Real.log_le_log (div_pos (hp'.trans_le h₁) hp')
        ((div_le_iff₀ hp').mpr (by linarith only [h₂]))⟩
    calc c*p = (p:ℝ)*c := mul_comm _ _
         _ ≤ B p j := mul_le_mul h₁ (hmin hlog) hc.le (sq_nonneg _)
  have hsum : x/2*(c*p) ≤ ∑ j ∈ Ioc 0 M, B p j := calc
    _ ≤ S.card*(c*p) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hc.le (Nat.cast_nonneg _))
    _ = ∑ _j ∈ S, c*p := by simp
    _ ≤ ∑ j ∈ S, B p j := sum_le_sum hterm
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => B_nonneg _ _
  exact (le_of_eq (show c*p=(2/x)*(x/2*(c*p)) by field_simp [hx.ne'])).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- Every sufficiently large prime p occurs in the reduced numerator of
each prefix beyond C√p, with valuation at least a fixed multiple of p. -/
theorem inner_primes_in_reduced_square_prefix : ∃ c A : ℝ, 0 < c ∧ 0 < A ∧
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ N : ℕ, A*Real.sqrt p ≤ N →
      c*p ≤ (deningerRatExp (squareGeneratorPrefix N) p:ℝ) := by
  obtain ⟨D,hD,hstab⟩ := large_prime_valuation_of_square_prefix_stabilizes
  obtain ⟨K,hK,hrow⟩ := row_lower
  obtain ⟨c,hc,hcentral⟩ := central_bump_mass
  let A := Real.exp 4+Real.sqrt D+3
  have hA : 2 ≤ A := by dsimp only [A]; linarith only [Real.exp_pos 4,Real.sqrt_nonneg D]
  have hT := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨c/2,A+1,half_pos hc,by linarith only [hA],?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (9*D),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (8+Real.log 9),
    hT.eventually_ge_atTop 2,hT.eventually_ge_atTop (2*K*(A+1)/c)] with p hbig hlarge htwo hcost
  intro hp N hN
  let x := Real.sqrt p
  let M := ⌈A*x⌉₊
  change 2 ≤ x at htwo
  change 2*K*(A+1)/c ≤ x at hcost
  have hx : 0 < x := two_pos.trans_le htwo
  have hpx : x^2=(p:ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hA₀ : 0 ≤ A := (by norm_num : (0:ℝ) ≤ 2).trans hA
  have hM : A*x ≤ (M:ℝ) := Nat.le_ceil _
  have hM' : (M:ℝ) ≤ (A+1)*x := by
    have hceil : (M:ℝ) < A*x+1 := Nat.ceil_lt_add_one (mul_nonneg hA₀ hx.le)
    linarith only [hceil,htwo]
  have hcut : Real.sqrt (D*p) ≤ M := by
    rw [Real.sqrt_mul (zero_le_one.trans hD)]
    exact (mul_le_mul_of_nonneg_right (show Real.sqrt D ≤ A by
      dsimp only [A]; linarith only [Real.exp_pos 4]) hx.le).trans hM
  have hvan (j : ℕ) (hj : M < j) : B p j=0 := by
    have hj' : Real.exp 4*x < (j:ℝ) :=
      ((mul_le_mul_of_nonneg_right (show Real.exp 4 ≤ A by dsimp only [A]; linarith only [Real.sqrt_nonneg D])
        hx.le).trans hM).trans_lt (Nat.cast_lt.mpr hj)
    have hsq := pow_lt_pow_left₀ hj' (mul_nonneg (Real.exp_pos _).le hx.le) (by decide : 2 ≠ 0)
    have he : Real.exp 4^2=Real.exp 8 := by
      rw [sq,← Real.exp_add]; norm_num
    rw [mul_pow,hpx,he] at hsq
    have h := Real.log_lt_log (mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr hp.pos)) hsq
    rw [Real.log_mul (Real.exp_pos _).ne' (Nat.cast_pos.mpr hp.pos).ne',Real.log_exp] at h
    unfold B bump
    rw [splineAutoCorr_zero_outside ((show 8 < Real.log ((j:ℝ)^2)-Real.log p by linarith only [h]).trans_le
      (le_abs_self _)),mul_zero]
  have H := sum_le_sum (s := Ioc 0 M) fun j hj => hrow hp (mem_Ioc.mp hj).1 hlarge
  simp only [sum_sub_distrib,← mul_sum,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul] at H
  have hcent := hcentral htwo ((mul_le_mul_of_nonneg_right hA hx.le).trans hM)
  have hodd := odd_sum_le hvan
  have hhalf : K*(M:ℝ) ≤ c/2*p := by
    have ht := (div_le_iff₀ hc).mp hcost
    have h₁ := mul_le_mul_of_nonneg_right ht hx.le
    rw [← hpx]
    linarith only [h₁,mul_le_mul_of_nonneg_left hM' hK]
  rw [hstab hbig hcut (Nat.cast_le.mp (hM'.trans hN)),squareGeneratorPrefix_valuation,Int.cast_sum]
  have hcomp := mul_le_mul_of_nonneg_left hodd (show 0 ≤ 2/Real.sqrt p by positivity)
  linarith only [H,hcent,hcomp,hhalf]

/-- The inner primes divide the numerator and are absent from the denominator
of the actual reduced rational prefix. -/
theorem inner_primes_divide_only_square_prefix_numerator : ∃ A : ℝ, 0 < A ∧
    ∀ᶠ p : ℕ in atTop, p.Prime → ∀ N : ℕ, A*Real.sqrt p ≤ N →
      p ∣ (squareGeneratorPrefix N).num.natAbs ∧ ¬p ∣ (squareGeneratorPrefix N).den := by
  obtain ⟨c,A,hc,hA,h⟩ := inner_primes_in_reduced_square_prefix
  refine ⟨A,hA,?_⟩
  filter_upwards [h] with p hp
  intro hprime N hN
  let r := squareGeneratorPrefix N
  have hpos : 0 < deningerRatExp r p := by
    exact_mod_cast (mul_pos hc (Nat.cast_pos.mpr hprime.pos)).trans_le (hp hprime N hN)
  rw [deningerRatExp_apply] at hpos
  have hnum : p ∣ r.num.natAbs := Nat.dvd_of_factorization_pos (by omega)
  refine ⟨hnum,fun hden => ?_⟩
  have hg := Nat.dvd_gcd hnum hden
  rw [r.reduced.gcd_eq_one] at hg
  exact hprime.ne_one (Nat.dvd_one.mp hg)

#print axioms inner_primes_in_reduced_square_prefix
#print axioms inner_primes_divide_only_square_prefix_numerator

end GaloisForLFunctions.CountingHolography.Sections
