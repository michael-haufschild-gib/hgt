import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.SquarefreePolynomialWeights
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.FiniteProductWeights
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.MonicPolynomialCoordinates
import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.StatementT

/-! The five local exceptional events control the joint
weight of tuples that fail the irreducibility criterion. -/

noncomputable section

open Finset Polynomial WindowedLandauTheory.CyclotomicNorms

namespace WindowedLandauTheory.ConcN

open FiniteWeight

variable (g N : ℕ) [Fact g.Prime]

def separatesPrimeToParts (c : Fin N → ZMod g) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ BB N g →
    ∀ x ∈ rootsBar (monicOf c), ∀ y ∈ rootsBar (monicOf c),
      primeToPart l x = primeToPart l y → x = y

def avoidsCharacter (c₀ : (ZMod g)ˣ) (c : Fin N → ZMod g) : Prop :=
  ∀ l : ℕ, l.Prime → l ≠ g → ∀ x ∈ rootsBar (monicOf c),
    primeToPart l x ≠ primeToPart l (algebraMap (ZMod g) (Fbar g) (c₀ : ZMod g))

def hasDivisorDegree (a : ℕ) (c : Fin N → ZMod g) : Prop :=
  ∃ Q : (ZMod g)[X], Q ∣ monicOf c ∧ Q.natDegree = a

def hasLongPrimeFactor (c : Fin N → ZMod g) : Prop :=
  ∃ Q : (ZMod g)[X], Irreducible Q ∧ Q ∣ monicOf c ∧ Q.natDegree.Prime ∧
    N < 2 * Q.natDegree ∧ Q.natDegree + 3 ≤ N

/-- Local squarefree mass, prime-component and factor-degree estimates. -/
structure LocalRowWeightBounds (q₁ d : ℕ) : Prop where
  mass : 1 - 2 / (g : ℝ) ≤ ∑ c ∈ squarefreeCoefficients g N, squarefreeWeight g (monicOf c)
  separation : open Classical in
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ separatesPrimeToParts g N c),
      squarefreeWeight g (monicOf c) ≤ 23 * Real.log g / Real.sqrt g
  avoid : ∀ c₀ : (ZMod g)ˣ, open Classical in
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ avoidsCharacter g N c₀ c),
      squarefreeWeight g (monicOf c) ≤ 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((g : ℝ) - 1)
  degree : ∀ a ∈ Icc 1 (N / 2), open Classical in
    ∑ c ∈ (squarefreeCoefficients g N).filter (hasDivisorDegree g N a), squarefreeWeight g (monicOf c) ≤ 7 / 8
  longPrime : open Classical in
    ∑ c ∈ (squarefreeCoefficients g N).filter (fun c => ¬ hasLongPrimeFactor g N c),
      squarefreeWeight g (monicOf c) ≤ 1 - 1 / (5 * Real.log N)

open Classical in
theorem local_bad_weight_le {ι J : Type} [Fintype ι] [Fintype J] (q₁ d : ℕ)
    (bounds : LocalRowWeightBounds g N q₁ d) (χ : ι → J → (ZMod g)ˣ) (P : (Fin N → ZMod g) → ℝ)
    (hP0 : ∀ c, 0 ≤ P c) (hP1 : ∑ c, P c = 1)
    (hPsq : ∀ c ∈ squarefreeCoefficients g N, P c = squarefreeWeight g (monicOf c)) :
    ∑ x ∈ univ.filter (fun x : ι → Fin N → ZMod g =>
      ¬ (IsGood N g (fun v => monicOf (x v)) χ ∧
        IsGood N g (fun v => monicOf (x v)) (fun v j => (χ v j)⁻¹))), ∏ v, P (x v) ≤
      2 * (Fintype.card ι : ℝ) / (g : ℝ) +
      23 * (Fintype.card ι : ℝ) * Real.log g / Real.sqrt g +
      2 * (Fintype.card ι : ℝ) * (Fintype.card J : ℝ) *
        (1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((g : ℝ) - 1)) +
      (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι +
      Real.exp (-(Fintype.card ι : ℝ) / (5 * Real.log N)) := by
  let Ω := Fin N → ZMod g
  have hμ : ∀ x : ι → Ω, 0 ≤ ∏ v, P (x v) :=
    fun x => Finset.prod_nonneg fun v _ => hP0 _
  have hconv (p : Ω → Prop) :
      weight P {c | c ∈ squarefreeCoefficients g N ∧ p c} =
      ∑ c ∈ (squarefreeCoefficients g N).filter p, squarefreeWeight g (monicOf c) := by
    rw [weight_eq_filter']
    exact Finset.sum_congr rfl fun c hc => hPsq c (Finset.mem_filter.1 hc).1
  let f : ℝ := Fintype.card ι
  let S1 : Set Ω := {c | c ∈ squarefreeCoefficients g N}ᶜ
  let S3 : Set Ω := {c | c ∈ squarefreeCoefficients g N ∧ ¬ separatesPrimeToParts g N c}
  let S4 (c₀ : (ZMod g)ˣ) : Set Ω := {c | c ∈ squarefreeCoefficients g N ∧ ¬ avoidsCharacter g N c₀ c}
  let S5 (a : ℕ) : Set Ω := {c | c ∈ squarefreeCoefficients g N ∧ hasDivisorDegree g N a c}
  let S6 : Set Ω := {c | c ∈ squarefreeCoefficients g N ∧ ¬ hasLongPrimeFactor g N c}
  have b1 : weight P S1 ≤ 2 / (g : ℝ) := by
    rw [show S1 = {c | c ∈ squarefreeCoefficients g N}ᶜ from rfl, weight_compl, weight_univ, hP1]
    have e : weight P {c | c ∈ squarefreeCoefficients g N} =
        ∑ c ∈ squarefreeCoefficients g N, squarefreeWeight g (monicOf c) := by
      simpa using hconv (fun _ => True)
    rw [e, sub_le_comm]
    exact bounds.mass
  have b3 : weight P S3 ≤ 23 * Real.log g / Real.sqrt g := by
    refine (hconv _).trans_le ?_
    convert bounds.separation
  have b4 (c₀ : (ZMod g)ˣ) : weight P (S4 c₀) ≤
      1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by
    refine (hconv _).trans_le ?_
    convert bounds.avoid c₀
  have b5 (a : ℕ) (ha : a ∈ Icc 1 (N / 2)) : weight P (S5 a) ≤ 7 / 8 :=
    (hconv _).trans_le (bounds.degree a ha)
  have b6 : weight P S6 ≤ 1 - 1 / (5 * Real.log N) := by
    refine (hconv _).trans_le ?_
    convert bounds.longPrime
  have hcover : {x : ι → Ω | ¬ (IsGood N g (fun v => monicOf (x v)) χ ∧
      IsGood N g (fun v => monicOf (x v)) (fun v j => (χ v j)⁻¹))} ⊆
      (((((⋃ v ∈ (univ : Finset ι), {x : ι → Ω | x v ∈ S1}) ∪
        (⋃ v ∈ (univ : Finset ι), {x : ι → Ω | x v ∈ S3})) ∪
        (⋃ w ∈ (univ : Finset (ι × J)), ({x : ι → Ω | x w.1 ∈ S4 (χ w.1 w.2)} ∪
          {x : ι → Ω | x w.1 ∈ S4 (χ w.1 w.2)⁻¹}))) ∪
        (⋃ a ∈ Icc 1 (N / 2), {x : ι → Ω | ∀ v, x v ∈ S5 a})) ∪
        {x : ι → Ω | ∀ v, x v ∈ S6}) := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists, Set.mem_setOf_eq,
      Finset.mem_univ, true_implies] at hcon
    obtain ⟨⟨⟨⟨c1, c3⟩, c4⟩, c5⟩, c6⟩ := hcon
    have hsq (v : ι) : x v ∈ squarefreeCoefficients g N := by
      simpa only [S1, Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using c1 v
    have hs (v : ι) : Squarefree (monicOf (x v)) ∧ (monicOf (x v)).coeff 0 ≠ 0 := by
      simpa [squarefreeCoefficients] using hsq v
    have hsep (v : ι) : separatesPrimeToParts g N (x v) :=
      not_not.mp fun h => c3 v ⟨hsq v, h⟩
    have hdiv (a : ℕ) (ha : 1 ≤ a) (ha' : 2 * a ≤ N) :
        ∃ v, ¬ hasDivisorDegree g N a (x v) := by
      by_contra hn
      push Not at hn
      exact c5 a (Finset.mem_Icc.mpr ⟨ha, by omega⟩) fun v => ⟨hsq v, hn v⟩
    have hlong : ∃ v, hasLongPrimeFactor g N (x v) := by
      by_contra hn
      exact c6 fun v => ⟨hsq v, fun hv => hn ⟨v, hv⟩⟩
    have good (ψ : ι → J → (ZMod g)ˣ) (hψ : ∀ v j, avoidsCharacter g N (ψ v j) (x v)) :
        IsGood N g (fun v => monicOf (x v)) ψ := by
      refine ⟨fun v => ⟨monic_monicOf _, natDegree_monicOf _, (hs v).2⟩,
        fun v => (hs v).1, ?_, ?_, hdiv, hlong⟩
      · intro l hl hn v
        exact hsep v l hl hn
      · intro l hl hn v j
        exact hψ v j l hl hn
    exact hx ⟨good χ fun v j => not_not.mp fun h => (c4 (v, j)).1 ⟨hsq v, h⟩,
      good (fun v j => (χ v j)⁻¹) fun v j => not_not.mp fun h => (c4 (v, j)).2 ⟨hsq v, h⟩⟩
  rw [← weight_eq_filter (fun x : ι → Ω => ∏ v, P (x v))
    (fun x => ¬ (IsGood N g (fun v => monicOf (x v)) χ ∧
      IsGood N g (fun v => monicOf (x v)) (fun v j => (χ v j)⁻¹)))]
  refine (weight_mono _ hμ hcover).trans ?_
  refine (weight_union_le _ hμ _ _).trans (add_le_add ((weight_union_le _ hμ _ _).trans
    (add_le_add ((weight_union_le _ hμ _ _).trans (add_le_add ((weight_union_le _ hμ _ _).trans
      (add_le_add ?_ ?_)) ?_)) ?_)) ?_)
  · refine (weight_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, weight (fun x : ι → Ω => ∏ v, P (x v)) {x | x v ∈ S1}
        = ∑ _v : ι, weight P S1 := Finset.sum_congr rfl fun v _ => weight_one_place P hP1 S1 v
      _ = f * weight P S1 := by simp [f]
      _ ≤ f * (2 / (g : ℝ)) := mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)
      _ = 2 * f / (g : ℝ) := by ring
  · refine (weight_biUnion_le _ hμ _ _).trans ?_
    calc ∑ v : ι, weight (fun x : ι → Ω => ∏ v, P (x v)) {x | x v ∈ S3}
        = ∑ _v : ι, weight P S3 := Finset.sum_congr rfl fun v _ => weight_one_place P hP1 S3 v
      _ = f * weight P S3 := by simp [f]
      _ ≤ f * (23 * Real.log g / Real.sqrt g) :=
          mul_le_mul_of_nonneg_left b3 (Nat.cast_nonneg _)
      _ = 23 * f * Real.log g / Real.sqrt g := by ring
  · refine (weight_biUnion_le _ hμ _ _).trans ?_
    set B : ℝ := 1 / (4 * (min q₁ d : ℕ)) + (1 + Real.log N) / ((g : ℝ) - 1) with hB
    calc ∑ w : ι × J, weight (fun x : ι → Ω => ∏ v, P (x v))
          ({x | x w.1 ∈ S4 (χ w.1 w.2)} ∪ {x | x w.1 ∈ S4 (χ w.1 w.2)⁻¹})
        ≤ ∑ _w : ι × J, (B + B) := by
          refine Finset.sum_le_sum fun w _ => (weight_union_le _ hμ _ _).trans (add_le_add ?_ ?_)
          · rw [weight_one_place P hP1]; exact b4 _
          · rw [weight_one_place P hP1]; exact b4 _
      _ = 2 * f * (Fintype.card J : ℝ) * B := by
          simp [f, Fintype.card_prod]; ring
  · refine (weight_biUnion_le _ hμ _ _).trans ?_
    calc ∑ a ∈ Finset.Icc 1 (N / 2), weight (fun x : ι → Ω => ∏ v, P (x v))
          {x | ∀ v, x v ∈ S5 a}
        ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [weight_pi P (fun _ => S5 a), Finset.prod_const, Finset.card_univ]
          exact pow_le_pow_left₀ (weight_nonneg P hP0 _) (b5 a ha) _
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8 : ℝ) ^ Fintype.card ι := by simp
      _ ≤ (N : ℝ) / 2 * (7 / 8 : ℝ) ^ Fintype.card ι := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Nat.cast_div_le
  · rw [weight_pi P (fun _ => S6), Finset.prod_const, Finset.card_univ]
    calc weight P S6 ^ Fintype.card ι ≤ (Real.exp (-(1 / (5 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ (weight_nonneg P hP0 _) (b6.trans ?_) _
          exact Real.one_sub_le_exp_neg _
      _ = Real.exp (-f / (5 * Real.log N)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          dsimp only [f]
          ring

end WindowedLandauTheory.ConcN

#print axioms WindowedLandauTheory.ConcN.local_bad_weight_le
