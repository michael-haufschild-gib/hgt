import GaloisForLFunctions.HTGeometry.NewtonEdgeNonCancellation

/-!
# Determinants on the logarithmic scale

A family of matrices measured on the logarithmic scale of a diverging radius has a determinant whose
exponent is read off the assignment problem for the matrix of entry exponents: if one permutation
gives a strictly larger total exponent than every other, the determinant has exactly that exponent,
and in particular does not vanish along the filter.

The consequence used for degenerations is the last theorem.  A perturbed matrix `M = m + r` whose
corrections are `o` of the corresponding model entries has the *model's* entry exponents, so a model
whose assignment problem has a unique optimum forces the perturbed determinant to be nonzero.  The
uniqueness of the optimum is exactly the statement that no cancellation occurs in the leading term
of the model determinant; without it the corrections can beat the surviving part of the model.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Asymptotics

/-- **Weights add over a finite product.** -/
theorem HasLogScaleExponent.prod
    {α ι : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {g : ι → α → ℂ} {w : ι → ℝ} (hg : ∀ i, HasLogScaleExponent l ρ (g i) (w i))
    (s : Finset ι) :
    HasLogScaleExponent l ρ (fun x => ∏ i ∈ s, g i x) (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasLogScaleExponent_const hρ (c := (1 : ℂ)) one_ne_zero
  | insert b t hb ih =>
      simp only [Finset.prod_insert hb, Finset.sum_insert hb]
      exact (hg b).mul ih

/-- **A negligible correction does not move the exponent.** -/
theorem HasLogScaleExponent.add_isLittleO
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {f g : α → ℂ} {a : ℝ} (hf : HasLogScaleExponent l ρ f a) (hg : g =o[l] f) :
    HasLogScaleExponent l ρ (fun x => f x + g x) a := by
  refine hf.of_tendsto_ratio_one hρ ?_
  have h1 : Tendsto (fun x => 1 + g x / f x) l (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := l)).add hg.tendsto_div_nhds_zero
  refine Tendsto.congr' ?_ h1
  filter_upwards [hf.1] with x hx
  field_simp

/-- The sign of a permutation is a nonzero complex number. -/
theorem sign_cast_ne_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> norm_num

/-- **The determinant reads off the optimal assignment.**  If the total exponent of one permutation
strictly exceeds that of every other, the determinant has exactly that exponent. -/
theorem hasLogScaleExponent_det_of_unique_max
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (hM : ∀ i k, HasLogScaleExponent l ρ (fun x => M x i k) (a i k))
    (σ₀ : Equiv.Perm (Fin n))
    (hmax : ∀ σ : Equiv.Perm (Fin n), σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    HasLogScaleExponent l ρ (fun x => (M x).det) (∑ i, a (σ₀ i) i) := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      HasLogScaleExponent l ρ
        (fun x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M x (σ i) i) (∑ i, a (σ i) i) := by
    intro σ
    have hp := HasLogScaleExponent.prod (g := fun i x => M x (σ i) i)
      (w := fun i => a (σ i) i) hρ (fun i => hM (σ i) i) Finset.univ
    have h := (hasLogScaleExponent_const hρ (sign_cast_ne_zero σ)).mul hp
    rwa [zero_add] at h
  have hsum := hasLogScaleExponent_sum_of_unique_max hρ
    (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M x (σ i) i)
    (fun σ => ∑ i, a (σ i) i) σ₀ (Finset.mem_univ _)
    (fun σ _ => hterm σ) (fun σ _ hσ => hmax σ hσ)
  refine hsum.congr' (Filter.Eventually.of_forall fun x => ?_)
  rw [Matrix.det_apply']

/-- **Nonvanishing from a unique optimal assignment.** -/
theorem det_ne_zero_of_unique_max_logScale
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (hM : ∀ i k, HasLogScaleExponent l ρ (fun x => M x i k) (a i k))
    (σ₀ : Equiv.Perm (Fin n))
    (hmax : ∀ σ : Equiv.Perm (Fin n), σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    ∀ᶠ x in l, (M x).det ≠ 0 :=
  (hasLogScaleExponent_det_of_unique_max hρ M a hM σ₀ hmax).1

/-- **The degeneration theorem.**  A matrix family whose entries differ from a model's by
corrections that are `o` of the model entries has the model's exponents; if the model's assignment
problem has a unique optimum, the perturbed determinant carries the model exponent and is
eventually nonzero.  No hypothesis on the size of the corrections beyond entrywise negligibility is
used: uniqueness of the optimum is what forbids a cancellation the corrections could exploit. -/
theorem hasLogScaleExponent_det_of_perturbation
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M m r : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (hsplit : ∀ x i k, M x i k = m x i k + r x i k)
    (hm : ∀ i k, HasLogScaleExponent l ρ (fun x => m x i k) (a i k))
    (hr : ∀ i k, (fun x => r x i k) =o[l] fun x => m x i k)
    (σ₀ : Equiv.Perm (Fin n))
    (hmax : ∀ σ : Equiv.Perm (Fin n), σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    HasLogScaleExponent l ρ (fun x => (M x).det) (∑ i, a (σ₀ i) i) := by
  refine hasLogScaleExponent_det_of_unique_max hρ M a (fun i k => ?_) σ₀ hmax
  refine ((hm i k).add_isLittleO hρ (hr i k)).congr' (Filter.Eventually.of_forall fun x => ?_)
  exact (hsplit x i k).symm

/-- The perturbed determinant is eventually nonzero. -/
theorem det_ne_zero_of_perturbation_unique_max
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M m r : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (hsplit : ∀ x i k, M x i k = m x i k + r x i k)
    (hm : ∀ i k, HasLogScaleExponent l ρ (fun x => m x i k) (a i k))
    (hr : ∀ i k, (fun x => r x i k) =o[l] fun x => m x i k)
    (σ₀ : Equiv.Perm (Fin n))
    (hmax : ∀ σ : Equiv.Perm (Fin n), σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    ∀ᶠ x in l, (M x).det ≠ 0 :=
  (hasLogScaleExponent_det_of_perturbation hρ M m r a hsplit hm hr σ₀ hmax).1

/-- The perturbation hypothesis in measured form: a correction of strictly smaller exponent is
negligible. -/
theorem isLittleO_of_lt_exponent
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {f g : α → ℂ} {a b : ℝ} (hf : HasLogScaleExponent l ρ f a)
    (hg : HasLogScaleExponent l ρ g b) (hab : b < a) : g =o[l] f :=
  isLittleO_of_hasLogScaleExponent_lt hρ hg hf hab

/-! ## Null entries

A Jacobian typically has entries that vanish identically, and those have no measured exponent.  The
assignment problem is then posed on the set of permutations that avoid every null entry, and the
remaining permutations contribute nothing to the determinant.
-/

/-- **The determinant reads off the optimal assignment among the surviving permutations.**  Every
permutation outside `S` has an identically vanishing product; among those in `S` one has a strictly
larger total exponent than the rest. -/
theorem hasLogScaleExponent_det_of_unique_max_on
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (S : Finset (Equiv.Perm (Fin n)))
    (hnull : ∀ σ ∉ S, ∀ᶠ x in l, ∏ i, M x (σ i) i = 0)
    (hM : ∀ σ ∈ S, ∀ i, HasLogScaleExponent l ρ (fun x => M x (σ i) i) (a (σ i) i))
    {σ₀ : Equiv.Perm (Fin n)} (hσ₀ : σ₀ ∈ S)
    (hmax : ∀ σ ∈ S, σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    HasLogScaleExponent l ρ (fun x => (M x).det) (∑ i, a (σ₀ i) i) := by
  classical
  have hterm : ∀ σ ∈ S,
      HasLogScaleExponent l ρ
        (fun x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M x (σ i) i) (∑ i, a (σ i) i) := by
    intro σ hσ
    have hp := HasLogScaleExponent.prod (g := fun i x => M x (σ i) i)
      (w := fun i => a (σ i) i) hρ (fun i => hM σ hσ i) Finset.univ
    have h := (hasLogScaleExponent_const hρ (sign_cast_ne_zero σ)).mul hp
    rwa [zero_add] at h
  have hsum := hasLogScaleExponent_sum_of_unique_max hρ S
    (fun σ x => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M x (σ i) i)
    (fun σ => ∑ i, a (σ i) i) σ₀ hσ₀ hterm hmax
  -- the permutations outside `S` contribute nothing
  have hall : ∀ᶠ x in l, ∀ σ ∈ (Finset.univ \ S), ∏ i, M x (σ i) i = 0 := by
    rw [Filter.eventually_all_finset]
    intro σ hσ
    exact hnull σ (Finset.mem_sdiff.mp hσ).2
  refine hsum.congr' ?_
  filter_upwards [hall] with x hx
  rw [Matrix.det_apply']
  refine Finset.sum_subset (Finset.subset_univ S) fun σ _ hσ => ?_
  rw [hx σ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hσ⟩), mul_zero]

/-- **The degeneration theorem with null entries.**  Off the null positions the entries differ from
the model's by corrections that are `o` of them; the null positions are killed in both. -/
theorem hasLogScaleExponent_det_of_perturbation_on
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M m r : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (S : Finset (Equiv.Perm (Fin n)))
    (hnull : ∀ σ ∉ S, ∀ᶠ x in l, ∏ i, M x (σ i) i = 0)
    (hsplit : ∀ σ ∈ S, ∀ x i, M x (σ i) i = m x (σ i) i + r x (σ i) i)
    (hm : ∀ σ ∈ S, ∀ i, HasLogScaleExponent l ρ (fun x => m x (σ i) i) (a (σ i) i))
    (hr : ∀ σ ∈ S, ∀ i, (fun x => r x (σ i) i) =o[l] fun x => m x (σ i) i)
    {σ₀ : Equiv.Perm (Fin n)} (hσ₀ : σ₀ ∈ S)
    (hmax : ∀ σ ∈ S, σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    HasLogScaleExponent l ρ (fun x => (M x).det) (∑ i, a (σ₀ i) i) := by
  refine hasLogScaleExponent_det_of_unique_max_on hρ M a S hnull (fun σ hσ i => ?_) hσ₀ hmax
  refine ((hm σ hσ i).add_isLittleO hρ (hr σ hσ i)).congr'
    (Filter.Eventually.of_forall fun x => ?_)
  exact (hsplit σ hσ x i).symm

/-- The perturbed determinant is eventually nonzero, with null entries allowed. -/
theorem det_ne_zero_of_perturbation_unique_max_on
    {α : Type*} {l : Filter α} {ρ : α → ℝ} (hρ : Tendsto ρ l atTop)
    {n : ℕ} (M m r : α → Matrix (Fin n) (Fin n) ℂ) (a : Fin n → Fin n → ℝ)
    (S : Finset (Equiv.Perm (Fin n)))
    (hnull : ∀ σ ∉ S, ∀ᶠ x in l, ∏ i, M x (σ i) i = 0)
    (hsplit : ∀ σ ∈ S, ∀ x i, M x (σ i) i = m x (σ i) i + r x (σ i) i)
    (hm : ∀ σ ∈ S, ∀ i, HasLogScaleExponent l ρ (fun x => m x (σ i) i) (a (σ i) i))
    (hr : ∀ σ ∈ S, ∀ i, (fun x => r x (σ i) i) =o[l] fun x => m x (σ i) i)
    {σ₀ : Equiv.Perm (Fin n)} (hσ₀ : σ₀ ∈ S)
    (hmax : ∀ σ ∈ S, σ ≠ σ₀ → ∑ i, a (σ i) i < ∑ i, a (σ₀ i) i) :
    ∀ᶠ x in l, (M x).det ≠ 0 :=
  (hasLogScaleExponent_det_of_perturbation_on hρ M m r a S hnull hsplit hm hr hσ₀ hmax).1

end GaloisForLFunctions.HTGeometry
