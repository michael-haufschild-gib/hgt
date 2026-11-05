import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheDecidingInputTheorem

/-!
# Bilinear norms are blind to multiplicative twists and relabelings

For a weight `a` and finite boxes `U`, `V` of positive integers, the Type II form is
`B_a(α, β) = Σ_{m ∈ U, n ∈ V} α_m β_n a(mn)`.  A Type II estimate is an inequality
`|B_a(α, β)| ≤ C ‖α‖₂ ‖β‖₂` for all coefficients; `bilinearConstants U V a` is the set of admissible `C`.

* **Twist invariance** (`bilinearConstants_twist`).  A completely multiplicative sign `g` conjugates the form,
  `B_{ga}(α, β) = B_a(gα, gβ)`, and preserves `ℓ²` norms.  So the admissible constants of `a` and `ga` agree at
  infinite precision on every box.  The Liouville twist is the case `g = λ`.
* **Exclusion** (`not_bilinearStatement_vonMangoldt`).  A property that sees a weight only through its admissible
  constants is parity-blind, so if it implies the count it fails at `Λ`: uniform Type II information
  cannot decide.
* **Stable test classes** (`classConstants_twist`).  A restriction to test vectors stable under the sign is equally blind, so a parity-breaking
  bilinear statement has to name a test class that is not stable under multiplicative signs.
* **Relabeling invariance** (`allBilinearConstants_comp`).  On unrestricted boxes the constants are also invariant under
  every completely multiplicative bijection of the positive integers, that is, under every permutation of the primes.
  Type II norms do not know where the primes are.
* **Locality on prime powers** (`bilinearForm_eq_zero_of_coprime`, `eq_pow_and_eq_pow_of_isPrimePow_mul`).  If `a` is
  supported on prime powers, its form on coprime boxes away from `1` vanishes identically, and only pairs from
  one prime tower interact.
* **The count kernel** (`sqrt_card_mul_card_le_of_mem_bilinearConstants_one`).  The kernel `a = 1` of the count is rank one:
  its best constant is the trivial `√(|U||V|)`, so it carries no Type II cancellation.
-/

noncomputable section

open Finset
open ArithmeticFunction (cardFactors)

namespace GaloisForLFunctions.ArithmeticProduction

open ArithmeticOfSquareRootPrecision

/-- The Type II form `B_a(α, β) = Σ α_m β_n a(mn)` on the box `U × V`. -/
def bilinearForm (U V : Finset ℕ) (a α β : ℕ → ℝ) : ℝ :=
  ∑ m ∈ U, ∑ n ∈ V, α m * β n * a (m * n)

/-- The `ℓ²` norm of a coefficient sequence on a finite set. -/
def ellTwo (U : Finset ℕ) (α : ℕ → ℝ) : ℝ := √(∑ m ∈ U, α m ^ 2)

/-- The admissible constants of Type II estimates for `a` on the box `U × V`. -/
def bilinearConstants (U V : Finset ℕ) (a : ℕ → ℝ) : Set ℝ :=
  {C | ∀ α β : ℕ → ℝ, |bilinearForm U V a α β| ≤ C * ellTwo U α * ellTwo V β}

/-- A sign that is completely multiplicative on the positive integers. -/
structure IsMultiplicativeSign (g : ℕ → ℝ) : Prop where
  mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → g (m * n) = g m * g n
  sq : ∀ {n : ℕ}, n ≠ 0 → g n ^ 2 = 1

/-- The Liouville function is a multiplicative sign. -/
theorem isMultiplicativeSign_liouville :
    IsMultiplicativeSign (fun n => ((-1 : ℝ)) ^ cardFactors n) where
  mul := fun hm hn => by
    simp only [ArithmeticFunction.cardFactors_mul hm hn, pow_add]
  sq := fun {n} _ => by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- A completely multiplicative sign conjugates the form. -/
theorem bilinearForm_sign_mul {U V : Finset ℕ} {g : ℕ → ℝ} (hg : IsMultiplicativeSign g)
    (hU : ∀ m ∈ U, m ≠ 0) (hV : ∀ n ∈ V, n ≠ 0) (a α β : ℕ → ℝ) :
    bilinearForm U V (fun n => g n * a n) α β =
      bilinearForm U V a (fun m => g m * α m) (fun n => g n * β n) := by
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  show α m * β n * (g (m * n) * a (m * n)) = g m * α m * (g n * β n) * a (m * n)
  rw [hg.mul (hU m hm) (hV n hn)]
  ring

theorem ellTwo_sign_mul {U : Finset ℕ} {g : ℕ → ℝ} (hg : IsMultiplicativeSign g)
    (hU : ∀ m ∈ U, m ≠ 0) (α : ℕ → ℝ) : ellTwo U (fun m => g m * α m) = ellTwo U α := by
  unfold ellTwo
  congr 1
  refine sum_congr rfl fun m hm => ?_
  rw [mul_pow, hg.sq (hU m hm), one_mul]

/-- **Twist invariance.**  A completely multiplicative sign does not change which Type II estimates hold. -/
theorem bilinearConstants_twist {U V : Finset ℕ} {g : ℕ → ℝ} (hg : IsMultiplicativeSign g)
    (hU : ∀ m ∈ U, m ≠ 0) (hV : ∀ n ∈ V, n ≠ 0) (a : ℕ → ℝ) :
    bilinearConstants U V (fun n => g n * a n) = bilinearConstants U V a := by
  ext C
  constructor
  · intro h α β
    have hinv : ∀ {W : Finset ℕ} (_ : ∀ k ∈ W, k ≠ 0) (γ : ℕ → ℝ) (k : ℕ), k ∈ W →
        g k * (g k * γ k) = γ k := fun hW γ k hk => by
      rw [← mul_assoc, ← sq, hg.sq (hW k hk), one_mul]
    have h1 := h (fun m => g m * α m) (fun n => g n * β n)
    rw [bilinearForm_sign_mul hg hU hV, ellTwo_sign_mul hg hU, ellTwo_sign_mul hg hV] at h1
    have hform : bilinearForm U V a (fun m => g m * (g m * α m)) (fun n => g n * (g n * β n)) =
        bilinearForm U V a α β := by
      refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
      show g m * (g m * α m) * (g n * (g n * β n)) * a (m * n) = α m * β n * a (m * n)
      rw [hinv hU α m hm, hinv hV β n hn]
    rwa [hform] at h1
  · intro h α β
    rw [bilinearForm_sign_mul hg hU hV]
    have h1 := h (fun m => g m * α m) (fun n => g n * β n)
    rwa [ellTwo_sign_mul hg hU, ellTwo_sign_mul hg hV] at h1

/-- The admissible constants of `a` and of its Liouville twist agree on every box of positive integers. -/
theorem bilinearConstants_liouvilleTwist {U V : Finset ℕ} (hU : ∀ m ∈ U, m ≠ 0)
    (hV : ∀ n ∈ V, n ≠ 0) (a : ℕ → ℝ) :
    bilinearConstants U V (liouvilleTwist a) = bilinearConstants U V a :=
  bilinearConstants_twist isMultiplicativeSign_liouville hU hV a

/-- A property of weights that sees a weight only through its Type II constants on boxes of positive integers. -/
def IsBilinearStatement (S : (ℕ → ℝ) → Prop) : Prop :=
  ∀ a b : ℕ → ℝ,
    (∀ U V : Finset ℕ, (∀ m ∈ U, m ≠ 0) → (∀ n ∈ V, n ≠ 0) →
      bilinearConstants U V a = bilinearConstants U V b) → (S a ↔ S b)

/-- A bilinear statement cannot tell a weight from its Liouville twist. -/
theorem IsBilinearStatement.iff_liouvilleTwist {S : (ℕ → ℝ) → Prop} (hS : IsBilinearStatement S)
    (a : ℕ → ℝ) : S (liouvilleTwist a) ↔ S a :=
  hS _ _ fun _ _ hU hV => bilinearConstants_liouvilleTwist hU hV a

/-- **Exclusion of Type II norms.**  A statement seeing weights only through Type II constants and implying the
count fails at `Λ`. -/
theorem not_bilinearStatement_vonMangoldt {S : (ℕ → ℝ) → Prop} (hS : IsBilinearStatement S)
    (hcount : ∀ a, S a → Count a) : ¬ S vonMangoldtWeight :=
  not_of_twist_stable S hcount fun a h => (hS.iff_liouvilleTwist a).mpr h

/-- The admissible constants of a Type II estimate restricted to a class of test vectors. -/
def classConstants (𝒞 : Set ((ℕ → ℝ) × (ℕ → ℝ))) (U V : Finset ℕ) (a : ℕ → ℝ) : Set ℝ :=
  {C | ∀ p ∈ 𝒞, |bilinearForm U V a p.1 p.2| ≤ C * ellTwo U p.1 * ellTwo V p.2}

/-- **A test class stable under the sign is still blind to it.**  So a parity-breaking bilinear statement must use test vectors whose class is not stable under multiplicative signs: it has to name them. -/
theorem classConstants_twist {𝒞 : Set ((ℕ → ℝ) × (ℕ → ℝ))} {U V : Finset ℕ} {g : ℕ → ℝ}
    (hg : IsMultiplicativeSign g) (hU : ∀ m ∈ U, m ≠ 0) (hV : ∀ n ∈ V, n ≠ 0)
    (h𝒞 : ∀ p ∈ 𝒞, ((fun m => g m * p.1 m), (fun n => g n * p.2 n)) ∈ 𝒞)
    (h𝒞' : ∀ p ∈ 𝒞, ∃ q ∈ 𝒞, ((fun m => g m * q.1 m), (fun n => g n * q.2 n)) = p) (a : ℕ → ℝ) :
    classConstants 𝒞 U V (fun n => g n * a n) = classConstants 𝒞 U V a := by
  ext C
  constructor
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := h𝒞' p hp
    have h1 := h q hq
    rw [bilinearForm_sign_mul hg hU hV] at h1
    simpa [ellTwo_sign_mul hg hU, ellTwo_sign_mul hg hV] using h1
  · intro h p hp
    have h1 := h _ (h𝒞 p hp)
    rw [bilinearForm_sign_mul hg hU hV]
    simpa [ellTwo_sign_mul hg hU, ellTwo_sign_mul hg hV] using h1

/-! ### Relabeling -/

/-- Admissible constants on all boxes of positive integers. -/
def allBilinearConstants (a : ℕ → ℝ) : Set ℝ :=
  {C | ∀ U V : Finset ℕ, (∀ m ∈ U, m ≠ 0) → (∀ n ∈ V, n ≠ 0) → C ∈ bilinearConstants U V a}

/-- A completely multiplicative bijection of the positive integers: the map induced by a permutation of the primes. -/
structure IsMultiplicativeRelabeling (ψ : ℕ ≃ ℕ) : Prop where
  mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → ψ (m * n) = ψ m * ψ n
  ne_zero : ∀ {n : ℕ}, n ≠ 0 → ψ n ≠ 0
  symm_ne_zero : ∀ {n : ℕ}, n ≠ 0 → ψ.symm n ≠ 0

private theorem IsMultiplicativeRelabeling.symm_mul {ψ : ℕ ≃ ℕ} (h : IsMultiplicativeRelabeling ψ)
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) : ψ.symm (m * n) = ψ.symm m * ψ.symm n := by
  apply ψ.injective
  rw [Equiv.apply_symm_apply, h.mul (h.symm_ne_zero hm) (h.symm_ne_zero hn),
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The inverse of a relabeling is a relabeling. -/
theorem IsMultiplicativeRelabeling.symm {ψ : ℕ ≃ ℕ} (h : IsMultiplicativeRelabeling ψ) :
    IsMultiplicativeRelabeling ψ.symm where
  mul := fun hm hn => h.symm_mul hm hn
  ne_zero := fun hn => h.symm_ne_zero hn
  symm_ne_zero := fun hn => h.ne_zero hn

private theorem allBilinearConstants_comp_subset {ψ : ℕ ≃ ℕ} (hψ : IsMultiplicativeRelabeling ψ)
    (a : ℕ → ℝ) : allBilinearConstants a ⊆ allBilinearConstants (a ∘ ψ) := by
  intro C hC U V hU hV α β
  have hU' : ∀ m ∈ U.map ψ.toEmbedding, m ≠ 0 := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hm
    exact hψ.ne_zero (hU k hk)
  have hV' : ∀ n ∈ V.map ψ.toEmbedding, n ≠ 0 := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hn
    exact hψ.ne_zero (hV k hk)
  have h := hC _ _ hU' hV' (α ∘ ψ.symm) (β ∘ ψ.symm)
  have hform : bilinearForm (U.map ψ.toEmbedding) (V.map ψ.toEmbedding) a (α ∘ ψ.symm) (β ∘ ψ.symm)
      = bilinearForm U V (a ∘ ψ) α β := by
    unfold bilinearForm
    rw [sum_map]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_map]
    refine sum_congr rfl fun n hn => ?_
    simp [hψ.mul (hU m hm) (hV n hn)]
  have hnorm : ∀ (W : Finset ℕ) (γ : ℕ → ℝ),
      ellTwo (W.map ψ.toEmbedding) (γ ∘ ψ.symm) = ellTwo W γ := by
    intro W γ
    unfold ellTwo
    rw [sum_map]
    simp
  rwa [hform, hnorm, hnorm] at h

/-- **Relabeling invariance.**  On unrestricted boxes the Type II constants are unchanged by every permutation of the
primes, extended multiplicatively. -/
theorem allBilinearConstants_comp {ψ : ℕ ≃ ℕ} (hψ : IsMultiplicativeRelabeling ψ) (a : ℕ → ℝ) :
    allBilinearConstants (a ∘ ψ) = allBilinearConstants a := by
  refine Set.Subset.antisymm ?_ (allBilinearConstants_comp_subset hψ a)
  have h := allBilinearConstants_comp_subset hψ.symm (a ∘ ψ)
  have he : (a ∘ ψ) ∘ ψ.symm = a := by
    funext n
    simp
  rwa [he] at h

/-! ### Locality on prime powers -/

/-- If `mn` is a prime power and `m, n ≠ 1`, then `m` and `n` lie in one prime tower. -/
theorem eq_pow_and_eq_pow_of_isPrimePow_mul {m n : ℕ} (h : IsPrimePow (m * n)) (hm : m ≠ 1)
    (hn : n ≠ 1) :
    ∃ p i j : ℕ, p.Prime ∧ 0 < i ∧ 0 < j ∧ m = p ^ i ∧ n = p ^ j := by
  obtain ⟨p, k, hp, _, hk⟩ := (isPrimePow_nat_iff _).mp h
  have hdm : m ∣ p ^ k := hk ▸ Dvd.intro n rfl
  have hdn : n ∣ p ^ k := hk ▸ Dvd.intro_left m rfl
  obtain ⟨i, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdm
  obtain ⟨j, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdn
  refine ⟨p, i, j, hp, Nat.pos_of_ne_zero ?_, Nat.pos_of_ne_zero ?_, rfl, rfl⟩
  · rintro rfl
    exact hm (pow_zero p)
  · rintro rfl
    exact hn (pow_zero p)

/-- **Locality.**  The form of a weight supported on prime powers vanishes on coprime boxes away from `1`.  In
particular the Type II form of `Λ` carries no information on such boxes. -/
theorem bilinearForm_eq_zero_of_coprime {U V : Finset ℕ} {a : ℕ → ℝ}
    (ha : ∀ n, ¬ IsPrimePow n → a n = 0) (hU : ∀ m ∈ U, m ≠ 1) (hV : ∀ n ∈ V, n ≠ 1)
    (hc : ∀ m ∈ U, ∀ n ∈ V, m.Coprime n) (α β : ℕ → ℝ) : bilinearForm U V a α β = 0 := by
  refine sum_eq_zero fun m hm => sum_eq_zero fun n hn => ?_
  rw [ha (m * n) ?_, mul_zero]
  intro hpp
  obtain ⟨p, i, j, hp, hi, hj, rfl, rfl⟩ := eq_pow_and_eq_pow_of_isPrimePow_mul hpp (hU _ hm) (hV _ hn)
  have hcop := hc _ hm _ hn
  have h1 : p ∣ Nat.gcd (p ^ i) (p ^ j) :=
    Nat.dvd_gcd (dvd_pow_self p hi.ne') (dvd_pow_self p hj.ne')
  rw [hcop] at h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

/-- The von Mangoldt function vanishes off prime powers. -/
theorem vonMangoldtWeight_eq_zero {n : ℕ} (hn : ¬ IsPrimePow n) : vonMangoldtWeight n = 0 :=
  ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn

/-! ### The count kernel -/

/-- **The count kernel is rank one.**  For `a ≡ 1` every admissible Type II constant is at least the trivial `√(|U||V|)`. -/
theorem sqrt_card_mul_card_le_of_mem_bilinearConstants_one {U V : Finset ℕ} {C : ℝ}
    (hC : C ∈ bilinearConstants U V (fun _ => 1)) (hU : U.Nonempty) (hV : V.Nonempty) :
    √((#U : ℝ) * #V) ≤ C := by
  have h := hC (fun _ => 1) (fun _ => 1)
  have hform : bilinearForm U V (fun _ => 1) (fun _ => 1) (fun _ => 1) = (#U : ℝ) * #V := by
    simp [bilinearForm]
  have hU0 : (0 : ℝ) < #U := by exact_mod_cast hU.card_pos
  have hV0 : (0 : ℝ) < #V := by exact_mod_cast hV.card_pos
  have hl : ∀ W : Finset ℕ, ellTwo W (fun _ => 1) = √(#W : ℝ) := by
    intro W
    simp [ellTwo]
  rw [hform, hl, hl, abs_of_pos (mul_pos hU0 hV0), mul_assoc, ← Real.sqrt_mul hU0.le] at h
  have hs : 0 < √((#U : ℝ) * #V) := Real.sqrt_pos.mpr (mul_pos hU0 hV0)
  have he : (#U : ℝ) * #V = √((#U : ℝ) * #V) * √((#U : ℝ) * #V) :=
    (Real.mul_self_sqrt (mul_pos hU0 hV0).le).symm
  by_contra hlt
  have hlt' := not_le.mp hlt
  nlinarith

end GaloisForLFunctions.ArithmeticProduction
