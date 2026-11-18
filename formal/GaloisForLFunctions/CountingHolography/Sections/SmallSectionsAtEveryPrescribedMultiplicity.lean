import GaloisForLFunctions.CountingHolography.Sections.PrimeMassAtFractionalLevels
import GaloisForLFunctions.CountingHolography.Sections.TheOuterBandOfSquareContacts
import GaloisForLFunctions.CountingHolography.Sections.TheCostsBeforeOrdinaryPrimeRounding
import GaloisForLFunctions.CountingHolography.Sections.OriginalSectionsOnTheSquareConductors

/-!
# Original sections at prescribed multiplicity

As the lag traverses the outer band, the contact crosses successive integer
levels. Primes on their negative sides pay for the ordinary floors at the
given multiplicity. The zero width controls the remaining signed degree.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology AbsoluteGeometryOfSpecZ ArithmeticFunction
open ArithmeticScatteringHolography SquareRootThreshold

/-- Every prescribed multiplicity with resolved level windows and small mesh
error has quadratic ordinary floor loss on the square conductors. -/
theorem successorSquare_floor_loss_at_prescribed_multiplicity {α d : ℝ}
    (hα : 7/12 < α) (hα' : α < 1) (hd : 0 < d) :
    ∃ c K : ℝ, 0 < c ∧ 1 ≤ K ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      let R := squareUpperRoot n
      let t := (m:ℝ)^2/R
      d ≤ t → K*(m:ℝ) ≤ R → K*t ≤ (R^2)^(1-α) →
      c*(n:ℝ)^2 ≤ ordinaryFloorLoss (m • successorSquareTriple n) := by
  obtain ⟨hu,huv,hcont,hfu,hfv,L,hL,hlip⟩ := outerSquareProfile_crosses
  obtain ⟨e,c,K₀,he,hc,hK₀,hbands⟩ := prime_floor_mass_of_profile_crossing
    hα hα' hu huv hL hd outerSquareProfile hcont hfu hfv hlip
  obtain ⟨E,hE,hread⟩ := successorSquare_outer_reading
  let K := max 1 (max K₀ (E/e))
  have hK : 1 ≤ K := le_max_left _ _
  have hK' : K₀ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hEK : E ≤ K*e := (div_le_iff₀ he).mp ((le_max_right _ _).trans (le_max_right _ _))
  have hnR (n : ℕ) : (n:ℝ) ≤ squareUpperRoot n := by
    unfold squareUpperRoot
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hBtop : Tendsto (fun n : ℕ => (squareUpperRoot n)^2) atTop atTop :=
    tendsto_atTop_mono (fun n => pow_le_pow_left₀ (Nat.cast_nonneg n) (hnR n) 2)
      ((tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop)
  refine ⟨c,K,hc,hK,?_⟩
  filter_upwards [hBtop.eventually hbands,eventually_ge_atTop 4] with n hn hn₄
  intro m hm
  let R := squareUpperRoot n
  let B := R^2
  let t := (m:ℝ)^2/R
  let P := contactBandPrimes (outerSquareLeft*B) ((outerSquareRight+1)*B)
  change d ≤ t → K*(m:ℝ) ≤ R → K*t ≤ B^(1-α) → _
  intro ht hmesh hscale
  have hR : 0 < R := by dsimp only [R,squareUpperRoot]; positivity
  have hB : 0 < B := sq_pos_of_pos hR
  have ht' : 0 < t := hd.trans_le ht
  have herr : E*(m:ℝ)/R ≤ e := (div_le_iff₀ hR).mpr (by
    linarith only [mul_le_mul_of_nonneg_right hEK (Nat.cast_nonneg (α := ℝ) m),
      mul_le_mul_of_nonneg_right hmesh he.le])
  have hu₀ := zero_lt_one.trans_le hu
  have hv₀ := hu₀.trans_le huv
  have hmem {p : ℕ} (hp : p ∈ P) : p.Prime ∧ outerSquareLeft*B < p ∧ (p:ℝ) ≤ (outerSquareRight+1)*B :=
    (mem_contactBandPrimes
    (mul_nonneg hu₀.le hB.le) (mul_nonneg (by linarith only [hv₀]) hB.le)).mp hp
  have hcontact {p : ℕ} (hp : p ∈ P) : 2 ≤ p ∧ p ≤ 3*windowEnd ((2*n+1)^2+1) ∧
      |successorSquareRawRow n m p + t*outerSquareProfile ((p:ℝ)/B)| ≤ E*m/R :=
    hread (k := p) hn₄ hm
    ((le_div_iff₀ hB).mpr (hmem hp).2.1.le) ((div_le_iff₀ hB).mpr (hmem hp).2.2)
  have hloss := hn ht ((mul_le_mul_of_nonneg_right hK' ht'.le).trans hscale)
    (successorSquareRawRow n m) (fun p hp => (hcontact hp).2.2.trans herr)
  have hsub : P ⊆ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)) := fun p hp =>
    mem_filter.mpr ⟨mem_Icc.mpr ⟨(hcontact hp).1,(hcontact hp).2.1⟩,(hmem hp).1⟩
  calc c*(n:ℝ)^2 ≤ c*B := mul_le_mul_of_nonneg_left
         (pow_le_pow_left₀ (Nat.cast_nonneg n) (hnR n) 2) hc.le
    _ ≤ ∑ p ∈ P, Int.fract (successorSquareRawRow n m p)*Real.log p := hloss
    _ = ∑ p ∈ P, Int.fract (successorSquareRawRow n m p)*vonMangoldt p := by
      refine sum_congr rfl fun p hp => ?_
      have hpr := (hmem hp).1
      rw [← log_contactBase,contactBase,if_pos hpr.isPrimePow,hpr.minFac_eq]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => mul_nonneg (Int.fract_nonneg _) vonMangoldt_nonneg)

/-- Exponentially many original sections exist at every positive multiplicity
within both the zero-width scale and the short-prime-interval scale. -/
theorem all_square_sections_at_width_and_prime_scales {α : ℝ} (hα : 7/12 < α) (hα' : α < 1) :
    ∃ K γ : ℝ, 1 ≤ K ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      K*(m:ℝ) ≤ ((n:ℝ)+1)^(1-zetaZeroWidth) → K*(m:ℝ) ≤ ((n:ℝ)+1)^(3/2-α) →
      let a := m • successorSquareTriple n
      Real.log (ordinaryPrimeGenerator a : ℝ) ≤ -(γ*(n:ℝ)^2) ∧
      Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a ∧
      2*⌊Real.exp (γ*(n:ℝ)^2)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨A₀,hA₀,hsmall⟩ := original_sections_on_successor_squares
  obtain ⟨A₁,_,hord⟩ := small_multiplicity_exponential_decay
  let A := max A₀ A₁
  have hA : 0 < A := hA₀.trans_le (le_max_left _ _)
  let d := 1/(3*A)
  have hd : 0 < d := by dsimp only [d]; positivity
  obtain ⟨c,J,hc,hJ,hfloor⟩ := successorSquare_floor_loss_at_prescribed_multiplicity hα hα' hd
  obtain ⟨E,hE,hcomp⟩ := square_cost_before_ordinary_floors
  let D := 1+J+8*E/c
  let γ := min (1/48:ℝ) (c/2)
  have hD : 1 ≤ D := by dsimp only [D]; linarith only [hJ,div_nonneg (by linarith only [hE] : 0 ≤ 8*E) hc.le]
  have hJD : J ≤ D := by dsimp only [D]; linarith only [div_nonneg (by linarith only [hE] : 0 ≤ 8*E) hc.le]
  have hED : 8*E ≤ D*c := (div_le_iff₀ hc).mp (by dsimp only [D]; linarith only [hJ])
  refine ⟨2*D,γ,by linarith only [hD],lt_min (by norm_num) (by positivity),?_⟩
  filter_upwards [hsmall,hord,hfloor,eventually_ge_atTop 1] with n hn ho hf hn₁
  intro m hm hw hs
  let R := squareUpperRoot n
  let g := ((n:ℝ)+1)^zetaZeroWidth
  let a := m • successorSquareTriple n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn₁
  have hn₀ := Nat.cast_nonneg (α := ℝ) n
  have hm₀ := Nat.cast_nonneg (α := ℝ) m
  have hX : 1 ≤ (n:ℝ)+1 := le_add_of_nonneg_left hn₀
  have hg : 1 ≤ g := Real.one_le_rpow hX zetaZeroWidth_nonneg
  have hg₀ := zero_le_one.trans hg
  have hmg₀ := mul_nonneg hm₀ hg₀
  have hR : 0 < R := by dsimp only [R,squareUpperRoot]; positivity
  have hfit : max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) ≤ -(γ*(n:ℝ)^2) := by
    by_cases ha : A*(m:ℝ)^2 ≤ n
    · have h := (hn hm ((mul_le_mul_of_nonneg_right (le_max_left A₀ A₁) (sq_nonneg (m:ℝ))).trans ha)).1
      have h' := ho hm ((mul_le_mul_of_nonneg_right (le_max_right A₀ A₁) (sq_nonneg (m:ℝ))).trans ha)
      have hγ := mul_le_mul_of_nonneg_right (min_le_left (1/48:ℝ) (c/2)) (sq_nonneg (n:ℝ))
      exact max_le (by linarith only [h',hγ,sq_nonneg (n:ℝ)]) (by linarith only [h,hγ])
    have hdt : d ≤ (m:ℝ)^2/R := by
      apply (div_le_div_iff₀ (by positivity : 0 < 3*A) hR).mpr
      dsimp only [R,squareUpperRoot]
      linarith only [lt_of_not_ge ha,hn']
    have hprod : ((n:ℝ)+1)^(1-zetaZeroWidth)*g=(n:ℝ)+1 := by
      unfold g
      rw [← Real.rpow_add (zero_lt_one.trans_le hX),sub_add_cancel,Real.rpow_one]
    have hb := mul_le_mul_of_nonneg_right hw hg₀
    rw [hprod] at hb
    have hDm : D*((m:ℝ)*g) ≤ n := by linarith only [hb,hn']
    have hmg : (m:ℝ)*g ≤ n := by linarith only [hDm,mul_le_mul_of_nonneg_right hD hmg₀]
    have hmle : (m:ℝ) ≤ (m:ℝ)*g := le_mul_of_one_le_right hm₀ hg
    have hJm : J*(m:ℝ) ≤ R := by
      dsimp only [R,squareUpperRoot]
      linarith only [hDm,hn₀,mul_le_mul_of_nonneg_right hJD hm₀,
        mul_le_mul_of_nonneg_left hmle (zero_le_one.trans hD)]
    have hEml : 8*E*((m:ℝ)*g) ≤ c*n := by
      linarith only [mul_le_mul_of_nonneg_right hED hmg₀,mul_le_mul_of_nonneg_right hDm hc.le]
    have hE₀ : 0 ≤ 8*E := by linarith only [hE]
    have hEl := (mul_le_mul_of_nonneg_left hmle hE₀).trans hEml
    have hquad := mul_le_mul hEml hmg hmg₀ (mul_nonneg hc.le hn₀)
    have hlin := mul_le_mul_of_nonneg_right hEl hn₀
    have hXR : (n:ℝ)+1 ≤ R := by dsimp only [R,squareUpperRoot]; linarith only [hn₀]
    have hscale := hs.trans (Real.rpow_le_rpow (zero_le_one.trans hX) hXR
      (by linarith only [hα'] : 0 ≤ 3/2-α))
    have hscale₂ := pow_le_pow_left₀ (mul_nonneg (by linarith only [hD] : 0 ≤ 2*D) hm₀) hscale 2
    have hpow : (R^(3/2-α))^2=(R^2)^(1-α)*R := by
      calc (R^(3/2-α))^2 = R^((3/2-α)*2) := by rw [Real.rpow_mul hR.le,Real.rpow_two]
        _ = R^(2*(1-α)+1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hR,Real.rpow_one,Real.rpow_mul hR.le,Real.rpow_two]
    rw [hpow] at hscale₂
    have hJ₂ : J ≤ (2*D)^2 := by
      linarith only [hJD,hD,sq_nonneg (D-1)]
    have hfreq : J*((m:ℝ)^2/R) ≤ (R^2)^(1-α) := by
      rw [← mul_div_assoc,div_le_iff₀ hR]
      linarith only [hscale₂,mul_le_mul_of_nonneg_right hJ₂ (sq_nonneg (m:ℝ))]
    have hl := hf hm hdt hJm hfreq
    have hh := hcomp hn₁ hm
    change max (Real.log (ordinaryPrimeGenerator a : ℝ)) (Real.log (generator a : ℝ)-radius a) +
      ordinaryFloorLoss a ≤ E*(((m:ℝ)*g)^2+(n:ℝ)*m) at hh
    linarith only [hh,hl,hquad,hlin,mul_le_mul_of_nonneg_right (min_le_right (1/48:ℝ) (c/2)) (sq_nonneg (n:ℝ)),
      mul_nonneg hc.le (sq_nonneg (n:ℝ))]
  obtain ⟨hord',hfull⟩ := max_le_iff.mp hfit
  refine ⟨hord',by linarith only [hfull],?_⟩
  have hpos : 0 < (generator a : ℝ) := by exact_mod_cast contactGenerator_pos _ _ _
  have hexp := Real.exp_le_exp.mpr (show γ*(n:ℝ)^2 ≤ radius a-Real.log (generator a : ℝ) by linarith only [hfull])
  rw [Real.exp_sub,Real.exp_log hpos] at hexp
  rw [card_smallSections]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.floor_mono hexp)) 1

/-- The unconditional width bound gives exponentially many original sections
at every prescribed multiplicity through a fixed multiple of (n+1)^(5/8). -/
theorem all_square_sections_through_five_eighths :
    ∃ K γ : ℝ, 1 ≤ K ∧ 0 < γ ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      K*(m:ℝ) ≤ ((n:ℝ)+1)^(5/8:ℝ) → let a := m • successorSquareTriple n
      Real.log (ordinaryPrimeGenerator a : ℝ) ≤ -(γ*(n:ℝ)^2) ∧
      Real.log (generator a : ℝ)+γ*(n:ℝ)^2 ≤ radius a ∧
      2*⌊Real.exp (γ*(n:ℝ)^2)⌋₊+1 ≤ (smallSections (generator a : ℝ) (radius a)).card := by
  obtain ⟨K,γ,hK,hγ,h⟩ := all_square_sections_at_width_and_prime_scales (α := 7/8) (by norm_num) (by norm_num)
  refine ⟨K,γ,hK,hγ,?_⟩
  filter_upwards [h] with n hn
  intro m hm hscale
  apply hn hm (hscale.trans (Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n))
    (by linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths])))
  simpa only [show (3/2:ℝ)-7/8=5/8 by norm_num] using hscale

#print axioms successorSquare_floor_loss_at_prescribed_multiplicity
#print axioms all_square_sections_at_width_and_prime_scales
#print axioms all_square_sections_through_five_eighths

end GaloisForLFunctions.CountingHolography.Sections
