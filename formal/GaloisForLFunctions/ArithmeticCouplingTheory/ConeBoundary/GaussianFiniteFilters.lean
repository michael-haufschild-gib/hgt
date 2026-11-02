import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.FiniteClockProducts
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.StripClockSeparation
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.GaussianZeroGeometry
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.GaussianResidues
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.GaussianFilterCosts

/-!
# Finite two-clock filters for actual zeros

Baker separation and the actual zero count give affine clock products that
isolate a fixed zero below height `n^4`. Both their values on the zero strip
and their action on bounded positive-clock moments cost at most `exp(K n^6)`.
-/

open Complex Finset
open Zeta23
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- A fixed actual zero remains polynomially separated in the two shifted prime clocks. -/
lemma exists_shifted_fixed_target_clock_lower {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (σ : ℝ)
    (ρ₀ : zetaZeroConfig.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∃ J : ℕ, ∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ →
      c/(2+|(ρ:ℂ).im-(ρ₀:ℂ).im|)^J ≤
        ‖shiftedClock σ (Real.log p) ρ-shiftedClock σ (Real.log p) ρ₀‖+
        ‖shiftedClock σ (Real.log q) ρ-shiftedClock σ (Real.log q) ρ₀‖ := by
  obtain ⟨r,hr,hisolate⟩ := exists_zeta_fixed_target_radius ρ₀
  obtain ⟨c,hc,J,hjoint⟩ := exists_strip_joint_clock_lower hp hq hpq (1/2+σ) hr
  refine ⟨c,hc,J,?_⟩
  intro ρ hne
  have hlow (ρ : zetaZeroConfig.carrier) : -(1/2+σ) ≤ (zeroOffset ρ-(σ:ℂ)).re := by
    rw [Complex.sub_re,Complex.ofReal_re,zeroOffset_re]
    linarith only [(zetaZeroConfig.strip ρ.val ρ.property).1]
  have he : (zeroOffset ρ-(σ:ℂ))-(zeroOffset ρ₀-(σ:ℂ))=(ρ:ℂ)-(ρ₀:ℂ) := by
    unfold zeroOffset
    ring
  have hh := hjoint (zeroOffset ρ-(σ:ℂ)) (zeroOffset ρ₀-(σ:ℂ))
    (hlow ρ) (hlow ρ₀) (by rw [he]; exact hisolate ρ hne)
  simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero,zeroOffset_im,shiftedClock] using hh

/-- The polynomially separated clock factors isolate one actual zero below a
fourth-power height cutoff, with sixth-power exponential cost. -/
theorem exists_actual_clock_filters {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {σ : ℝ} (hσ : 0 ≤ σ)
    (ρ₀ : zetaZeroConfig.carrier) :
    ∃ K R : ℝ, 0 < K ∧ 1 ≤ R ∧ |(ρ₀:ℂ).im| ≤ R ∧
      ∀ n : ℕ, R ≤ (n:ℝ) → ∃ P : zetaZeroConfig.carrier → ℂ,
        P ρ₀=1 ∧
        (∀ ρ : zetaZeroConfig.carrier, ρ ≠ ρ₀ → |(ρ:ℂ).im| ≤ (n:ℝ)^4 → P ρ=0) ∧
        (∀ ρ, ‖P ρ‖ ≤ Real.exp (K*(n:ℝ)^6)) ∧
        (∀ (d : zetaZeroConfig.carrier → ℂ) (M : ℝ),
          (∀ m l : ℕ, Summable (fun ρ => d ρ*shiftedClock σ (Real.log p) ρ^m*
            shiftedClock σ (Real.log q) ρ^l)) →
          (∀ m l : ℕ, ‖∑' ρ, d ρ*shiftedClock σ (Real.log p) ρ^m*
            shiftedClock σ (Real.log q) ρ^l‖ ≤ M) →
          ∀ m l : ℕ,
            Summable (fun ρ => d ρ*P ρ*shiftedClock σ (Real.log p) ρ^m*
              shiftedClock σ (Real.log q) ρ^l) ∧
            ‖∑' ρ, d ρ*P ρ*shiftedClock σ (Real.log p) ρ^m*
              shiftedClock σ (Real.log q) ρ^l‖ ≤ M*Real.exp (K*(n:ℝ)^6)) := by
  classical
  let a := Real.log p
  let b := Real.log q
  have ha : 0 ≤ a := (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hb : 0 ≤ b := (Real.log_pos (by exact_mod_cast hq.one_lt)).le
  let U := shiftedClock σ a
  let V := shiftedClock σ b
  let L := 1+Real.exp (a/2)+Real.exp (b/2)
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [Real.exp_pos (a/2),Real.exp_pos (b/2)]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hU (ρ : zetaZeroConfig.carrier) : ‖U ρ‖ ≤ L :=
    (norm_shiftedClock_le hσ ha ρ).trans (by dsimp only [L]; linarith only [Real.exp_pos (b/2)])
  have hV (ρ : zetaZeroConfig.carrier) : ‖V ρ‖ ≤ L :=
    (norm_shiftedClock_le hσ hb ρ).trans (by dsimp only [L]; linarith only [Real.exp_pos (a/2)])
  obtain ⟨c,hc,J,hgap⟩ := exists_shifted_fixed_target_clock_lower hp hq hpq σ ρ₀
  obtain ⟨C,R₀,hC,hR₀,hcount⟩ := exists_zeta_fourth_cutoff_count
  let B := 3+|(ρ₀:ℂ).im|
  have hB : 0 < B := by dsimp only [B]; positivity
  let Q := 2*(L+1)*B^J/c
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let A := L*Q+(4*J:ℕ)
  have hA : 0 < A := by dsimp only [A]; positivity
  let R := max R₀ (1+|(ρ₀:ℂ).im|)
  refine ⟨A*C,R,mul_pos hA hC,hR₀.trans (le_max_left _ _),
    (by dsimp only [R]; exact (show |(ρ₀:ℂ).im| ≤ 1+|(ρ₀:ℂ).im| by linarith).trans (le_max_right _ _)),?_⟩
  intro n hn
  have hnR : R₀ ≤ (n:ℝ) := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ (n:ℝ) := hR₀.trans hnR
  have hn0 : 0 < (n:ℝ) := zero_lt_one.trans_le hn1
  have hn4 : 1 ≤ (n:ℝ)^4 := one_le_pow₀ hn1
  let F := (RHTower.lowZeros_finite ((n:ℝ)^4)).toFinset.erase (ρ₀:ℂ)
  have hF (z : F) : z.val ∈ zetaZeroConfig.carrier ∧ |z.val.im| ≤ (n:ℝ)^4 := by
    have hz : z.val ∈ RHTower.lowZeros ((n:ℝ)^4) :=
      (Set.Finite.mem_toFinset (RHTower.lowZeros_finite ((n:ℝ)^4))).mp
        (mem_erase.mp z.property).2
    exact hz
  let atom (z : F) : zetaZeroConfig.carrier := ⟨z.val,(hF z).1⟩
  have hne (z : F) : atom z ≠ ρ₀ := fun he =>
    (mem_erase.mp z.property).1 (congrArg Subtype.val he)
  have hden (z : F) : 2+|z.val.im-(ρ₀:ℂ).im| ≤ B*(n:ℝ)^4 := by
    have hh : |z.val.im-(ρ₀:ℂ).im| ≤ |z.val.im|+|(ρ₀:ℂ).im| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le z.val.im (-(ρ₀:ℂ).im)
    have hm := mul_le_mul_of_nonneg_left hn4 (show 0 ≤ 2+|(ρ₀:ℂ).im| by positivity)
    dsimp only [B]
    nlinarith only [hh,(hF z).2,hm]
  let δ := c/(B*(n:ℝ)^4)^J
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsep (z : F) : δ ≤ ‖U ρ₀-U (atom z)‖+‖V ρ₀-V (atom z)‖ := by
    have hpoly : δ ≤ c/(2+|z.val.im-(ρ₀:ℂ).im|)^J :=
      div_le_div_of_nonneg_left hc.le (pow_pos (by positivity) J)
        (pow_le_pow_left₀ (by positivity) (hden z) J)
    have hh := hpoly.trans (hgap (atom z) (hne z))
    simpa only [norm_sub_rev] using hh
  have hfactor (z : F) := exists_affine_clock_separator hδ (hsep z) (hU (atom z)) (hV (atom z))
  choose c₀ c₁ c₂ hzero hone hcoeff using hfactor
  have hcost : 2*(L+1)/δ=Q*(n:ℝ)^(4*J) := by
    dsimp only [δ,Q]
    rw [mul_pow,← pow_mul]
    field_simp [hc.ne',hB.ne',hn0.ne']
  have hpoly : L*(Q*(n:ℝ)^(4*J)) ≤ Real.exp (A*(n:ℝ)) := by
    simpa only [A,mul_assoc] using polynomial_le_exp_linear (mul_pos hL0 hQ).le hn1 (4*J)
  have hcoef (z : F) : ‖c₀ z‖+‖c₁ z‖+‖c₂ z‖ ≤ Real.exp (A*(n:ℝ)) := by
    have hh := hcoeff z
    rw [hcost] at hh
    exact hh.trans ((le_mul_of_one_le_left (by positivity) hL1).trans hpoly)
  have hvalue (z : F) (ρ : zetaZeroConfig.carrier) :
      ‖c₀ z+c₁ z*U ρ+c₂ z*V ρ‖ ≤ Real.exp (A*(n:ℝ)) := by
    have hh := hcoeff z
    rw [hcost] at hh
    exact (norm_affine_clocks_le hL1 (hU ρ) (hV ρ)).trans
      ((mul_le_mul_of_nonneg_left hh hL0.le).trans hpoly)
  have hcard : (Fintype.card F:ℝ) ≤ C*(n:ℝ)^5 := by
    have hh : F.card ≤ ((RHTower.lowZeros_finite ((n:ℝ)^4)).toFinset).card := card_erase_le
    have hc' := hcount n hnR
    rw [Set.ncard_eq_toFinset_card _ (RHTower.lowZeros_finite ((n:ℝ)^4))] at hc'
    rw [Fintype.card_coe]
    exact (Nat.cast_le.mpr hh).trans hc'
  have htotal : (Real.exp (A*(n:ℝ)))^(Fintype.card F) ≤ Real.exp (A*C*(n:ℝ)^6) :=
    gaussian_clock_product_cost hA.le hn0.le hcard
  let P (ρ : zetaZeroConfig.carrier) := ∏ z : F, (c₀ z+c₁ z*U ρ+c₂ z*V ρ)
  have hprod : (∏ z : F, (‖c₀ z‖+‖c₁ z‖+‖c₂ z‖)) ≤ Real.exp (A*C*(n:ℝ)^6) := by
    calc
      _ ≤ ∏ _z : F, Real.exp (A*(n:ℝ)) := prod_le_prod (fun _ _ => by positivity) (fun z _ => hcoef z)
      _ = (Real.exp (A*(n:ℝ)))^(Fintype.card F) := by simp only [prod_const,card_univ]
      _ ≤ _ := htotal
  refine ⟨P,?_,?_,?_,?_⟩
  · exact prod_eq_one fun z _ => hone z
  · intro ρ hρ hheight
    have hraw : (ρ:ℂ) ∈ F := mem_erase.mpr ⟨by exact fun he => hρ (Subtype.ext he),
      (Set.Finite.mem_toFinset _).mpr ⟨ρ.property,hheight⟩⟩
    let z : F := ⟨ρ.val,hraw⟩
    have he : atom z=ρ := rfl
    exact prod_eq_zero (mem_univ z) (by simpa only [he] using hzero z)
  · intro ρ
    dsimp only [P]
    rw [norm_prod]
    calc
      _ ≤ ∏ _z : F, Real.exp (A*(n:ℝ)) := prod_le_prod (fun _ _ => norm_nonneg _) (fun z _ => hvalue z ρ)
      _ = (Real.exp (A*(n:ℝ)))^(Fintype.card F) := by simp only [prod_const,card_univ]
      _ ≤ _ := htotal
  · intro d M hs hM m l
    have hh := clock_product_moment_bound d U V c₀ c₁ c₂ hs hM univ m l
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
    exact ⟨hh.1,hh.2.trans (mul_le_mul_of_nonneg_left hprod hM0)⟩

#print axioms exists_shifted_fixed_target_clock_lower
#print axioms exists_actual_clock_filters
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
