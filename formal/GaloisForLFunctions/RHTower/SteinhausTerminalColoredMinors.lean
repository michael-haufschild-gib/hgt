import GaloisForLFunctions.HTGeometry.ComplexGramColoredMinors
import GaloisForLFunctions.RHTower.SteinhausFiniteNodeCovariance
import GaloisForLFunctions.RHTower.SteinhausTerminalSampleCounting

/-!
# Colored terminal minors in the finite-node arithmetic Gram form

Prime--cofactor feature indices are ordered first by their represented integer `p*m`.  Therefore
normalized-product intervals with ordered, nonoverlapping endpoints are strictly separated color
blocks.  The abstract colored Pluecker bound then turns every determinant floor on their
transversals into a product-cardinality lower bound for the actual arithmetic Gram determinant.
-/

namespace RHTower

open Finset GaloisForLFunctions.HTGeometry

noncomputable section

/-- Prime--cofactor features whose represented integer lies in the normalized interval `(a,b]`. -/
def steinhausFiniteNodeNormalizedProductBlock
    (P : Finset ℕ) (a b : ℝ) (N : ℕ) :
    Finset (steinhausFiniteNodeFeatureIndex P N) :=
  Finset.univ.filter fun q =>
    a * (N : ℝ) < (q.1.1 * q.1.2 : ℕ) ∧
      ((q.1.1 * q.1.2 : ℕ) : ℝ) ≤ b * (N : ℝ)

@[simp]
theorem mem_steinhausFiniteNodeNormalizedProductBlock
    {P : Finset ℕ} {a b : ℝ} {N : ℕ}
    {q : steinhausFiniteNodeFeatureIndex P N} :
    q ∈ steinhausFiniteNodeNormalizedProductBlock P a b N ↔
      a * (N : ℝ) < (q.1.1 * q.1.2 : ℕ) ∧
        ((q.1.1 * q.1.2 : ℕ) : ℝ) ≤ b * (N : ℝ) := by
  simp [steinhausFiniteNodeNormalizedProductBlock]

/-- The flattened cofactor blocks inject into the corresponding normalized-product feature block.
The upper endpoint assumption keeps every chosen cofactor inside the ambient range `m ≤ N/p`. -/
theorem sum_normalizedProductCofactorBlock_card_le_featureBlock_card
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (N : ℕ) :
    ∑ p ∈ P, (normalizedProductCofactorBlock a b N p).card ≤
      (steinhausFiniteNodeNormalizedProductBlock P a b N).card := by
  let A : Finset (Σ _ : ℕ, ℕ) := P.sigma fun p => normalizedProductCofactorBlock a b N p
  let B : Finset (steinhausFiniteNodeFeatureIndex P N) :=
    steinhausFiniteNodeNormalizedProductBlock P a b N
  let f : ↥A → ↥B := fun x => by
    have hx : x.1 ∈ P.sigma (fun p => normalizedProductCofactorBlock a b N p) := x.2
    rw [Finset.mem_sigma] at hx
    have hp := hP x.1.1 hx.1
    have hb0 : 0 ≤ b := le_trans ha hab.le
    have hm := (mem_normalizedProductCofactorBlock ha hb0 hp).mp hx.2
    have hpR : (0 : ℝ) < (x.1.1 : ℕ) := by exact_mod_cast hp
    have hmposR : (0 : ℝ) < (x.1.2 : ℕ) :=
      lt_of_le_of_lt (by positivity) hm.1
    have hmpos : 1 ≤ x.1.2 := by exact_mod_cast hmposR
    have hbN : b * (N : ℝ) ≤ (N : ℝ) := by
      simpa using mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg N)
    have hmNreal : (x.1.2 : ℕ) ≤ (N : ℝ) / (x.1.1 : ℕ) :=
      hm.2.trans (div_le_div_of_nonneg_right hbN hpR.le)
    have hmulReal : (((x.1.2 * x.1.1 : ℕ) : ℝ)) ≤ (N : ℝ) := by
      calc
        (((x.1.2 * x.1.1 : ℕ) : ℝ)) =
            (x.1.2 : ℝ) * (x.1.1 : ℝ) := by norm_num
        _ ≤ ((N : ℝ) / (x.1.1 : ℕ)) * (x.1.1 : ℝ) :=
          mul_le_mul_of_nonneg_right hmNreal hpR.le
        _ = (N : ℝ) := div_mul_cancel₀ _ hpR.ne'
    have hmul : x.1.2 * x.1.1 ≤ N := by exact_mod_cast hmulReal
    have hmN : x.1.2 ≤ N / x.1.1 :=
      (Nat.le_div_iff_mul_le hp).mpr hmul
    have hfull : x.1 ∈ P.sigma (fun p => Finset.Icc 1 (N / p)) :=
      Finset.mem_sigma.mpr ⟨hx.1, Finset.mem_Icc.mpr ⟨hmpos, hmN⟩⟩
    have hlo : a * (N : ℝ) < ((x.1.1 * x.1.2 : ℕ) : ℝ) := by
      have := (div_lt_iff₀ hpR).mp hm.1
      simpa [Nat.cast_mul, mul_comm] using this
    have hhi : (((x.1.1 * x.1.2 : ℕ) : ℝ)) ≤ b * (N : ℝ) := by
      have := (le_div_iff₀ hpR).mp hm.2
      simpa [Nat.cast_mul, mul_comm] using this
    exact ⟨⟨x.1, hfull⟩,
      (mem_steinhausFiniteNodeNormalizedProductBlock).mpr ⟨hlo, hhi⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥B => z.1.1) hxy
  calc
    ∑ p ∈ P, (normalizedProductCofactorBlock a b N p).card = A.card := by
      simp [A]
    _ ≤ B.card := Finset.card_le_card_of_injective hf
    _ = (steinhausFiniteNodeNormalizedProductBlock P a b N).card := rfl

/-- Every fixed normalized interval inside `(0,1]` contains linearly many actual terminal feature
indices, not merely a linearly large flattened cofactor count. -/
theorem exists_eventually_terminal_normalizedProductFeatureBlock_card_linear
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in Filter.atTop,
      c * (N : ℝ) ≤
        ((steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) a b N).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ :=
    exists_eventually_terminalPrimePowerWindow_normalizedProductCofactorBlock_card_linear ha hab
  refine ⟨c, hc, ?_⟩
  filter_upwards [hcount] with N hN
  have hcardNat := sum_normalizedProductCofactorBlock_card_le_featureBlock_card
    ha hab hb (terminalPrimePowerWindow N)
    (fun p hp => (mem_terminalPrimePowerWindow.mp hp).1.pos) N
  have hcardReal :
      (∑ p ∈ terminalPrimePowerWindow N,
        ((normalizedProductCofactorBlock a b N p).card : ℝ)) ≤
        ((steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) a b N).card : ℝ) := by
    exact_mod_cast hcardNat
  exact hN.trans hcardReal

/-- Finitely many fixed normalized intervals provide `N^J` colored terminal transversals. -/
theorem exists_eventually_prod_terminal_normalizedProductFeatureBlock_card_ge_pow
    {J : ℕ} {a b : Fin J → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j < b j) (hb : ∀ j, b j ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      C * (N : ℝ) ^ J ≤
        ((∏ j, (steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) (a j) (b j) N).card : ℕ) : ℝ) := by
  choose c hc hcount using fun j =>
    exists_eventually_terminal_normalizedProductFeatureBlock_card_linear
      (ha j) (hab j) (hb j)
  let C : ℝ := ∏ j, c j
  have hC : 0 < C := Finset.prod_pos fun j hj => hc j
  refine ⟨C, hC, ?_⟩
  have hallMem : ∀ᶠ N : ℕ in Filter.atTop, ∀ j ∈ (Finset.univ : Finset (Fin J)),
      c j * (N : ℝ) ≤
        ((steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) (a j) (b j) N).card : ℝ) :=
    (Finset.univ.eventually_all).mpr fun j hj => hcount j
  have hall : ∀ᶠ N : ℕ in Filter.atTop, ∀ j : Fin J,
      c j * (N : ℝ) ≤
        ((steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) (a j) (b j) N).card : ℝ) :=
    hallMem.mono fun N hN j => hN j (Finset.mem_univ j)
  filter_upwards [hall] with N hN
  calc
    C * (N : ℝ) ^ J = ∏ j : Fin J, (c j * (N : ℝ)) := by
      simp [C, Finset.prod_mul_distrib]
    _ ≤ ∏ j : Fin J,
        ((steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) (a j) (b j) N).card : ℝ) := by
      exact Finset.prod_le_prod
        (fun j hj => mul_nonneg (hc j).le (Nat.cast_nonneg N))
        (fun j hj => hN j)
    _ = ((∏ j, (steinhausFiniteNodeNormalizedProductBlock
          (terminalPrimePowerWindow N) (a j) (b j) N).card : ℕ) : ℝ) := by
      push_cast
      rfl

/-- Ordered nonoverlapping normalized intervals are strictly separated in the product-first
prime--cofactor feature order. -/
theorem steinhausFiniteNodeNormalizedProductBlock_strictlySeparated
    {J : ℕ} (P : Finset ℕ) (a b : Fin J → ℝ) (N : ℕ)
    (hsep : ∀ i j : Fin J, i < j → b i ≤ a j) :
    ∀ i j : Fin J, i < j →
      ∀ x ∈ steinhausFiniteNodeNormalizedProductBlock P (a i) (b i) N,
      ∀ y ∈ steinhausFiniteNodeNormalizedProductBlock P (a j) (b j) N, x < y := by
  intro i j hij x hx y hy
  rw [mem_steinhausFiniteNodeNormalizedProductBlock] at hx hy
  apply steinhausFiniteNodeFeatureIndex_lt_of_product_lt
  have hmiddle : b i * (N : ℝ) ≤ a j * (N : ℝ) :=
    mul_le_mul_of_nonneg_right (hsep i j hij) (Nat.cast_nonneg N)
  have hxy : ((x.1.1 * x.1.2 : ℕ) : ℝ) < ((y.1.1 * y.1.2 : ℕ) : ℝ) :=
    lt_of_le_of_lt (hx.2.trans hmiddle) hy.1
  exact_mod_cast hxy

/-- **Terminal colored-minor Gram bound.** A common determinant floor on all transversals of
ordered normalized-product blocks is multiplied by their product cardinality in the literal
finite-node arithmetic Gram determinant. -/
theorem prod_normalizedProductBlock_card_mul_sq_le_arithmeticGram_det_re
    {J : ℕ} (P : Finset ℕ) (a b : Fin J → ℝ) (N : ℕ)
    (hsep : ∀ i j : Fin J, i < j → b i ≤ a j)
    (coeff : Fin J → ℕ → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hminor : ∀ q : ∀ j, ↥(steinhausFiniteNodeNormalizedProductBlock P (a j) (b j) N),
      c ≤ ‖(Matrix.of fun i j => coeff i ((q j).1.1.1 * (q j).1.1.2)).det‖) :
    ((∏ j, (steinhausFiniteNodeNormalizedProductBlock P (a j) (b j) N).card : ℕ) : ℝ) *
        c ^ (2 : ℕ) ≤ (steinhausFiniteNodeArithmeticGram P coeff N).det.re := by
  let S : Fin J → Finset (steinhausFiniteNodeFeatureIndex P N) :=
    fun j => steinhausFiniteNodeNormalizedProductBlock P (a j) (b j) N
  have hSsep : ∀ i j : Fin J, i < j → ∀ x ∈ S i, ∀ y ∈ S j, x < y :=
    steinhausFiniteNodeNormalizedProductBlock_strictlySeparated P a b N hsep
  have hbound := prod_card_mul_sq_le_hermPluckerNormSq_of_coloredChoices
    (steinhausFiniteNodeFeature P coeff N) S hSsep hc (by
      intro q
      simpa [S, steinhausFiniteNodeFeature] using hminor q)
  calc
    ((∏ j, (steinhausFiniteNodeNormalizedProductBlock P (a j) (b j) N).card : ℕ) : ℝ) *
          c ^ (2 : ℕ) = ((∏ j, (S j).card : ℕ) : ℝ) * c ^ (2 : ℕ) := by rfl
    _ ≤ hermPluckerNormSq (steinhausFiniteNodeFeature P coeff N) := hbound
    _ = (steinhausFiniteNodeArithmeticGram P coeff N).det.re := by
      rw [det_steinhausFiniteNodeArithmeticGram_eq_pluckerNormSq]
      simp

end

end RHTower
