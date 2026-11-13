import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionInduction

/-!
# The Frobenius traces of an induced function

For a subgroup `I` of a finite group, an element `φ` of its normalizer and a function `χ`,

  `S(χ; I, g) = Σ_{τ ∈ I} χ(g τ)`   (`cosetSum`),   `a_m(χ; I, φ) = S(χ; I, φ^m) / |I|`
  (`frobeniusTrace`).

For the character of a representation `V`, `a_m` is the trace of `φ^m` on the invariants `V^I`,
so the `a_m` are the coefficients of the logarithm of the local Euler factor
`det(1 − T φ | V^I)^{-1} = exp(Σ_m a_m T^m / m)`.

Let `H` be a subgroup and `ψ` a function on `H`, extended by zero.

* **Residue degree** (`cosetMeets_iff_dvd`). The exponents `m` for which the coset `φ^m I`
  meets `H` are the multiples of one number `f ≥ 1` (`residueDegree`): they contain the order of
  `φ`, are closed under addition, and `m + n`, `n` among them give `m`.
* **One coset** (`cosetSum_extendByZero`). Let `φ' ∈ H ∩ φ^f I` and `I' = H ∩ I`. Then
  `S(ψ°; I, φ^m) = S(ψ; I', φ'^{m/f})` if `f ∣ m`, and `0` otherwise: `φ'^k ∈ φ^{fk} I`, and
  `φ'^k τ ∈ H` iff `τ ∈ H`.
* **Induction** (`cosetSum_inducedFunction_pow`). With the residue degree `f_x`, a Frobenius
  element `φ_x ∈ H` and the inertia `I_x = H ∩ x I x⁻¹` of the pair `(x I x⁻¹, x φ x⁻¹)`,

  `S(Ind ψ; I, φ^m) = |H|⁻¹ Σ_{x ∈ G, f_x ∣ m} S(ψ; I_x, φ_x^{m/f_x})`.
* **Index** (`card_subgroupOf_mul_residueDegree`). If `D` is the union of the cosets `φ^m I`
  and `n` is the order of `φ` modulo `I`, then `|H ∩ D| f = |H ∩ I| n`: the residue degree is
  the index of the image of `H ∩ D` in `D / I`.

This is the group theory of Artin's theorem that the Euler factor of an induced character at a
prime is the product of the Euler factors of the character at the primes above it, in the
variables `T^{f}`.
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

section CosetSum

variable {Γ : Type u} [Group Γ] [Fintype Γ]

/-- The sum of a function over the coset `g I`. -/
def cosetSum (χ : Γ → ℂ) (I : Subgroup Γ) (g : Γ) : ℂ := ∑ τ : I, χ (g * τ)

/-- The Frobenius trace `a_m(χ; I, φ)`: the mean of `χ` over the coset `φ^m I`. -/
def frobeniusTrace (χ : Γ → ℂ) (I : Subgroup Γ) (φ : Γ) (m : ℕ) : ℂ :=
  (Nat.card I : ℂ)⁻¹ * cosetSum χ I (φ ^ m)

/-- The sum over a coset does not depend on the representative. -/
theorem cosetSum_mul_mem (χ : Γ → ℂ) (I : Subgroup Γ) (g : Γ) {τ₀ : Γ} (h : τ₀ ∈ I) :
    cosetSum χ I (g * τ₀) = cosetSum χ I g := by
  unfold cosetSum
  rw [← Equiv.sum_comp (Equiv.mulLeft (⟨τ₀, h⟩ : I)) fun τ : I => χ (g * τ)]
  exact Finset.sum_congr rfl fun τ _ => by
    simp only [Equiv.coe_mulLeft, Subgroup.coe_mul, mul_assoc]

variable {I : Subgroup Γ}

omit [Fintype Γ] in
theorem conj_mem_of_mem_normalizer {g : Γ} (hg : g ∈ Subgroup.normalizer (I : Set Γ)) {τ : Γ} (hτ : τ ∈ I) :
    g * τ * g⁻¹ ∈ I :=
  (Subgroup.mem_normalizer_iff.mp hg τ).mp hτ

omit [Fintype Γ] in
theorem inv_conj_mem_of_mem_normalizer {g : Γ} (hg : g ∈ Subgroup.normalizer (I : Set Γ)) {τ : Γ} (hτ : τ ∈ I) :
    g⁻¹ * τ * g ∈ I := by
  have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) τ).mp hτ
  rwa [inv_inv] at h

omit [Fintype Γ] in
/-- Powers of an element of the coset `g I` lie in the cosets of the powers of `g`. -/
theorem exists_pow_mul_mem {g : Γ} (hg : g ∈ Subgroup.normalizer (I : Set Γ)) {τ : Γ} (hτ : τ ∈ I) (k : ℕ) :
    ∃ τ' ∈ I, (g * τ) ^ k = g ^ k * τ' := by
  induction k with
  | zero => exact ⟨1, I.one_mem, by rw [pow_zero, pow_zero, one_mul]⟩
  | succ k ih =>
    obtain ⟨τ', hτ', h⟩ := ih
    refine ⟨g⁻¹ * τ' * g * τ, I.mul_mem (inv_conj_mem_of_mem_normalizer hg hτ') hτ, ?_⟩
    rw [pow_succ, h, pow_succ]
    simp only [mul_assoc, mul_inv_cancel_left]

/-! ### The residue degree -/

/-- The coset `φ^m I` meets `H`. -/
def CosetMeets (I : Subgroup Γ) (φ : Γ) (H : Subgroup Γ) (m : ℕ) : Prop :=
  ∃ τ ∈ I, φ ^ m * τ ∈ H

variable {φ : Γ} {H : Subgroup Γ}

omit [Fintype Γ] in
theorem cosetMeets_zero : CosetMeets I φ H 0 :=
  ⟨1, I.one_mem, by rw [pow_zero, one_mul]; exact H.one_mem⟩

omit [Fintype Γ] in
theorem CosetMeets.add (hφ : φ ∈ Subgroup.normalizer (I : Set Γ)) {m n : ℕ} (hm : CosetMeets I φ H m)
    (hn : CosetMeets I φ H n) : CosetMeets I φ H (m + n) := by
  obtain ⟨τ, hτ, h⟩ := hm
  obtain ⟨τ', hτ', h'⟩ := hn
  refine ⟨(φ ^ n)⁻¹ * τ * φ ^ n * τ',
    I.mul_mem (inv_conj_mem_of_mem_normalizer (pow_mem hφ n) hτ) hτ', ?_⟩
  have e : φ ^ (m + n) * ((φ ^ n)⁻¹ * τ * φ ^ n * τ') = φ ^ m * τ * (φ ^ n * τ') := by
    rw [pow_add]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e]
  exact H.mul_mem h h'

omit [Fintype Γ] in
theorem CosetMeets.sub (hφ : φ ∈ Subgroup.normalizer (I : Set Γ)) {m n : ℕ} (hmn : CosetMeets I φ H (m + n))
    (hn : CosetMeets I φ H n) : CosetMeets I φ H m := by
  obtain ⟨τ, hτ, h⟩ := hmn
  obtain ⟨τ', hτ', h'⟩ := hn
  refine ⟨φ ^ n * (τ * τ'⁻¹) * (φ ^ n)⁻¹,
    conj_mem_of_mem_normalizer (pow_mem hφ n) (I.mul_mem hτ (I.inv_mem hτ')), ?_⟩
  have e : φ ^ m * (φ ^ n * (τ * τ'⁻¹) * (φ ^ n)⁻¹) = φ ^ (m + n) * τ * (φ ^ n * τ')⁻¹ := by
    rw [pow_add, mul_inv_rev]
    simp only [mul_assoc]
  rw [e]
  exact H.mul_mem h (H.inv_mem h')

omit [Fintype Γ] in
theorem CosetMeets.mul (hφ : φ ∈ Subgroup.normalizer (I : Set Γ)) {n : ℕ} (hn : CosetMeets I φ H n) (k : ℕ) :
    CosetMeets I φ H (n * k) := by
  induction k with
  | zero => exact cosetMeets_zero
  | succ k ih =>
    rw [Nat.mul_succ]
    exact ih.add hφ hn

theorem exists_pos_cosetMeets (I : Subgroup Γ) (φ : Γ) (H : Subgroup Γ) :
    ∃ n, 0 < n ∧ CosetMeets I φ H n :=
  ⟨orderOf φ, orderOf_pos φ, 1, I.one_mem, by
    rw [pow_orderOf_eq_one, one_mul]
    exact H.one_mem⟩

/-- The residue degree: the least `f ≥ 1` such that the coset `φ^f I` meets `H`. -/
def residueDegree (I : Subgroup Γ) (φ : Γ) (H : Subgroup Γ) : ℕ :=
  Nat.find (exists_pos_cosetMeets I φ H)

theorem residueDegree_pos (I : Subgroup Γ) (φ : Γ) (H : Subgroup Γ) :
    0 < residueDegree I φ H :=
  (Nat.find_spec (exists_pos_cosetMeets I φ H)).1

theorem cosetMeets_residueDegree (I : Subgroup Γ) (φ : Γ) (H : Subgroup Γ) :
    CosetMeets I φ H (residueDegree I φ H) :=
  (Nat.find_spec (exists_pos_cosetMeets I φ H)).2

/-- **The cosets `φ^m I` that meet `H` are those with `f ∣ m`.** -/
theorem cosetMeets_iff_dvd (hφ : φ ∈ Subgroup.normalizer (I : Set Γ)) {m : ℕ} :
    CosetMeets I φ H m ↔ residueDegree I φ H ∣ m := by
  constructor
  · intro hm
    have hq : CosetMeets I φ H (residueDegree I φ H * (m / residueDegree I φ H)) :=
      (cosetMeets_residueDegree I φ H).mul hφ _
    -- the remainder is an exponent below the least positive one
    have hr : CosetMeets I φ H (m % residueDegree I φ H) := by
      have h : CosetMeets I φ H
          (m % residueDegree I φ H + residueDegree I φ H * (m / residueDegree I φ H)) := by
        rwa [Nat.mod_add_div]
      exact h.sub hφ hq
    by_contra hdvd
    have hpos : 0 < m % residueDegree I φ H :=
      Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
    have hle := Nat.find_min' (exists_pos_cosetMeets I φ H) ⟨hpos, hr⟩
    exact absurd (Nat.mod_lt m (residueDegree_pos I φ H)) (not_lt.mpr hle)
  · rintro ⟨k, rfl⟩
    exact (cosetMeets_residueDegree I φ H).mul hφ k

/-- The residue degree is the positive exponent of a meeting coset that divides all others. -/
theorem residueDegree_eq_of_dvd (hφ : φ ∈ Subgroup.normalizer (I : Set Γ)) {f : ℕ} (hf : CosetMeets I φ H f)
    (hmin : ∀ m, CosetMeets I φ H m → f ∣ m) : residueDegree I φ H = f :=
  Nat.dvd_antisymm ((cosetMeets_iff_dvd hφ).mp hf) (hmin _ (cosetMeets_residueDegree I φ H))

end CosetSum

/-! ### One coset -/

section Induction

variable {G : Type u} [Group G] [Fintype G] (H : Subgroup G)

/-- If the coset does not meet `H`, the sum of an extension by zero over it vanishes. -/
theorem cosetSum_extendByZero_eq_zero (ψ : H → ℂ) {I : Subgroup G} {φ : G} {m : ℕ}
    (h : ¬CosetMeets I φ H m) : cosetSum (extendByZero H ψ) I (φ ^ m) = 0 :=
  Finset.sum_eq_zero fun τ _ => extendByZero_of_notMem H ψ fun hmem => h ⟨τ, τ.2, hmem⟩

/-- The sum of an extension by zero over the coset of an element of `H` is the sum over the
coset of the intersection. -/
theorem cosetSum_extendByZero_coe (ψ : H → ℂ) {I : Subgroup G} {I' : Subgroup H}
    (hI' : ∀ h : H, h ∈ I' ↔ (h : G) ∈ I) (g : H) :
    cosetSum (extendByZero H ψ) I (g : G) = cosetSum ψ I' g := by
  unfold cosetSum
  symm
  refine Fintype.sum_of_injective (fun τ : I' => (⟨((τ : H) : G), (hI' τ).mp τ.2⟩ : I)) ?_ _ _
    ?_ ?_
  · intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun t : I => (t : G)) hab))
  · intro τ hτ
    refine extendByZero_of_notMem H ψ fun hmem => hτ ?_
    have hτH : (τ : G) ∈ H := by
      have h := H.mul_mem (H.inv_mem g.2) hmem
      rwa [inv_mul_cancel_left] at h
    exact ⟨⟨⟨τ, hτH⟩, (hI' _).mpr τ.2⟩, Subtype.ext rfl⟩
  · intro τ
    rw [extendByZero_of_mem H ψ (H.mul_mem g.2 (τ : H).2)]
    rfl

/-- **The sum over the coset `φ^{fk} I`** for a Frobenius element `φ' ∈ H ∩ φ^f I`. -/
theorem cosetSum_extendByZero_pow (ψ : H → ℂ) {I : Subgroup G} {φ : G} (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    {I' : Subgroup H} (hI' : ∀ h : H, h ∈ I' ↔ (h : G) ∈ I) {f : ℕ} {φ' : H} {τ₀ : G}
    (hτ₀ : τ₀ ∈ I) (hφ' : (φ' : G) = φ ^ f * τ₀) (k : ℕ) :
    cosetSum (extendByZero H ψ) I (φ ^ (f * k)) = cosetSum ψ I' (φ' ^ k) := by
  obtain ⟨τk, hτk, hk⟩ := exists_pow_mul_mem (pow_mem hφ f) hτ₀ k
  have e : ((φ' ^ k : H) : G) = φ ^ (f * k) * τk := by
    rw [Subgroup.coe_pow, hφ', hk, pow_mul]
  rw [← cosetSum_mul_mem _ I _ hτk, ← e]
  exact cosetSum_extendByZero_coe H ψ hI' (φ' ^ k)

/-- **The sum of an extension by zero over a coset of the powers of `φ`.** -/
theorem cosetSum_extendByZero (ψ : H → ℂ) {I : Subgroup G} {φ : G} (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    {I' : Subgroup H} (hI' : ∀ h : H, h ∈ I' ↔ (h : G) ∈ I) {φ' : H} {τ₀ : G} (hτ₀ : τ₀ ∈ I)
    (hφ' : (φ' : G) = φ ^ residueDegree I φ H * τ₀) (m : ℕ) :
    cosetSum (extendByZero H ψ) I (φ ^ m) =
      if residueDegree I φ H ∣ m then cosetSum ψ I' (φ' ^ (m / residueDegree I φ H)) else 0 := by
  split_ifs with hd
  · obtain ⟨k, rfl⟩ := hd
    rw [Nat.mul_div_cancel_left k (residueDegree_pos I φ H)]
    exact cosetSum_extendByZero_pow H ψ hφ hI' hτ₀ hφ' k
  · exact cosetSum_extendByZero_eq_zero H ψ fun hm => hd ((cosetMeets_iff_dvd hφ).mp hm)

/-! ### Conjugates -/

omit [Fintype G] in
/-- The conjugate of an element of the normalizer normalizes the conjugate subgroup. -/
theorem conj_mem_normalizer_map_conj {I : Subgroup G} {φ : G} (hφ : φ ∈ Subgroup.normalizer (I : Set G)) (x : G) :
    x * φ * x⁻¹ ∈
      Subgroup.normalizer ((I.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    MulAut.conj_symm_apply, Subgroup.mem_normalizer_iff.mp hφ (x⁻¹ * h * x)]
  have e : x⁻¹ * (x * φ * x⁻¹ * h * (x * φ * x⁻¹)⁻¹) * x = φ * (x⁻¹ * h * x) * φ⁻¹ := by
    group
  rw [e]

/-- The sum over a coset, conjugated, is the sum over the coset of the conjugate subgroup. -/
theorem sum_conj_eq_cosetSum (F : G → ℂ) (I : Subgroup G) (x g : G) :
    ∑ τ : I, F (x * (g * τ) * x⁻¹) =
      cosetSum F (I.map (MulAut.conj x).toMonoidHom) (x * g * x⁻¹) := by
  unfold cosetSum
  rw [← Equiv.sum_comp
    (I.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective).toEquiv]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, Subgroup.coe_equivMapOfInjective_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  congr 1
  simp only [mul_assoc, inv_mul_cancel_left]

/-- **The sum of an induced function over a coset** is the mean over the group of the sums of
the function over the conjugate cosets. -/
theorem cosetSum_inducedFunction (ψ : H → ℂ) (I : Subgroup G) (g : G) :
    cosetSum (inducedFunction H ψ) I g =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        cosetSum (extendByZero H ψ) (I.map (MulAut.conj x).toMonoidHom) (x * g * x⁻¹) := by
  unfold cosetSum inducedFunction
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun x _ => sum_conj_eq_cosetSum (extendByZero H ψ) I x g

/-! ### The Frobenius traces of an induced function -/

/-- The residue degree at the conjugate by `x`. -/
def residueDegreeAt (I : Subgroup G) (φ x : G) : ℕ :=
  residueDegree (I.map (MulAut.conj x).toMonoidHom) (x * φ * x⁻¹) H

theorem exists_frobeniusAt (I : Subgroup G) (φ x : G) :
    ∃ φ' : H, ∃ τ₀ ∈ I.map (MulAut.conj x).toMonoidHom,
      (φ' : G) = (x * φ * x⁻¹) ^ residueDegreeAt H I φ x * τ₀ := by
  obtain ⟨τ, hτ, h⟩ :=
    cosetMeets_residueDegree (I.map (MulAut.conj x).toMonoidHom) (x * φ * x⁻¹) H
  exact ⟨⟨_, h⟩, τ, hτ, rfl⟩

/-- A Frobenius element of `H` at the conjugate by `x`: an element of `H` in the coset
`(x φ x⁻¹)^f (x I x⁻¹)`. -/
def frobeniusAt (I : Subgroup G) (φ x : G) : H :=
  Classical.choose (exists_frobeniusAt H I φ x)

theorem frobeniusAt_spec (I : Subgroup G) (φ x : G) :
    ∃ τ₀ ∈ I.map (MulAut.conj x).toMonoidHom,
      (frobeniusAt H I φ x : G) = (x * φ * x⁻¹) ^ residueDegreeAt H I φ x * τ₀ :=
  Classical.choose_spec (exists_frobeniusAt H I φ x)

/-- **The Frobenius traces of an induced function**:
`S(Ind ψ; I, φ^m) = |H|⁻¹ Σ_{x, f_x ∣ m} S(ψ; H ∩ x I x⁻¹, φ_x^{m/f_x})`. -/
theorem cosetSum_inducedFunction_pow (ψ : H → ℂ) {I : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G)) (m : ℕ) :
    cosetSum (inducedFunction H ψ) I (φ ^ m) =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        if residueDegreeAt H I φ x ∣ m then
          cosetSum ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
            (frobeniusAt H I φ x ^ (m / residueDegreeAt H I φ x))
        else 0 := by
  rw [cosetSum_inducedFunction]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  obtain ⟨τ₀, hτ₀, hφ'⟩ := frobeniusAt_spec H I φ x
  have hpow : x * φ ^ m * x⁻¹ = (x * φ * x⁻¹) ^ m := (conj_pow (a := x) (b := φ) (i := m)).symm
  rw [hpow]
  exact cosetSum_extendByZero H ψ (conj_mem_normalizer_map_conj hφ x)
    (fun _ => Subgroup.mem_subgroupOf) hτ₀ hφ' m

/-- The same for the Frobenius traces: the weights are `|H ∩ x I x⁻¹| / (|I| |H|)`. -/
theorem frobeniusTrace_inducedFunction (ψ : H → ℂ) {I : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G)) (m : ℕ) :
    frobeniusTrace (inducedFunction H ψ) I φ m =
      (Nat.card I : ℂ)⁻¹ * (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        if residueDegreeAt H I φ x ∣ m then
          (Nat.card ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H) : ℂ) *
            frobeniusTrace ψ ((I.map (MulAut.conj x).toMonoidHom).subgroupOf H)
              (frobeniusAt H I φ x) (m / residueDegreeAt H I φ x)
        else 0 := by
  rw [frobeniusTrace, cosetSum_inducedFunction_pow H ψ hφ m, mul_assoc]
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [frobeniusTrace, ← mul_assoc, mul_inv_cancel₀, one_mul]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  · rfl

/-! ### The index of the decomposition group of a subgroup

Let `D` be the union of the cosets `φ^m I`. Its cosets by `I` are `φ^m I` for `m < n`, with `n`
the least positive exponent with `φ^n ∈ I`. Counting the elements of `H ∩ D` coset by coset gives
`|H ∩ D| f = |H ∩ I| n`: the residue degree is the index of the image of `H ∩ D` in `D / I`. -/

/-- A sum over the multiples of `f` below `f r`. -/
theorem sum_range_mul_ite_dvd {f : ℕ} (hf : 0 < f) (r : ℕ) (c : ℂ) :
    ∑ m ∈ Finset.range (f * r), (if f ∣ m then c else 0) = r * c := by
  have himage : (Finset.range (f * r)).filter (fun m => f ∣ m) =
      (Finset.range r).image (fun k => f * k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hm, k, rfl⟩
      exact ⟨k, lt_of_mul_lt_mul_left hm (Nat.zero_le f), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left hk hf, dvd_mul_right f k⟩
  rw [← Finset.sum_filter, Finset.sum_const, himage,
    Finset.card_image_of_injective _ fun a b h => Nat.eq_of_mul_eq_mul_left hf h,
    Finset.card_range, nsmul_eq_mul]

/-- The least positive power of `φ` in `I`. -/
theorem pow_residueDegree_self_mem (I : Subgroup G) (φ : G) : φ ^ residueDegree I φ I ∈ I := by
  obtain ⟨τ, hτ, h⟩ := cosetMeets_residueDegree I φ I
  have h2 := I.mul_mem h (I.inv_mem hτ)
  rwa [mul_inv_cancel_right] at h2

/-- **The cosets of `I` in the group generated by `I` and `φ`**: a sum over it is the sum of
the sums over the cosets `φ^m I`, `m < n`. -/
theorem cosetSum_one_eq_sum_range (F : G → ℂ) {I D : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ) :
    cosetSum F D 1 = ∑ m ∈ Finset.range (residueDegree I φ I), cosetSum F I (φ ^ m) := by
  have hn := pow_residueDegree_self_mem I φ
  unfold cosetSum
  rw [Finset.sum_sigma']
  symm
  refine Finset.sum_bij (fun (a : Σ _ : ℕ, I) _ => (⟨φ ^ a.1 * a.2, (hgen _).mpr
    ⟨a.1, a.2, a.2.2, rfl⟩⟩ : D)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · -- two cosets `φ^m I`, `φ^{m'} I` with `m, m' < n` that meet are equal
    have key : ∀ (m m' : ℕ) (τ τ' : I), m ≤ m' → m' < residueDegree I φ I →
        φ ^ m * (τ : G) = φ ^ m' * (τ' : G) → m = m' := by
      intro m m' τ τ' hle hlt h
      have hmem : φ ^ (m' - m) ∈ I := by
        have e : φ ^ (m' - m) = (τ : G) * (τ' : G)⁻¹ := by
          have h2 : φ ^ m' = φ ^ m * φ ^ (m' - m) := by
            rw [← pow_add, Nat.add_sub_cancel' hle]
          rw [h2, mul_assoc] at h
          have h3 := mul_left_cancel h
          rw [h3, mul_inv_cancel_right]
        rw [e]
        exact I.mul_mem τ.2 (I.inv_mem τ'.2)
      have hdvd : residueDegree I φ I ∣ m' - m :=
        (cosetMeets_iff_dvd hφ).mp ⟨1, I.one_mem, by rwa [mul_one]⟩
      have h0 : m' - m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    rintro ⟨m, τ⟩ ha ⟨m', τ'⟩ ha' h
    have hm := Finset.mem_range.mp (Finset.mem_sigma.mp ha).1
    have hm' := Finset.mem_range.mp (Finset.mem_sigma.mp ha').1
    have hG : φ ^ m * (τ : G) = φ ^ m' * (τ' : G) := congrArg (fun d : D => (d : G)) h
    have hmm : m = m' := by
      rcases Nat.le_total m m' with hle | hle
      · exact key m m' τ τ' hle hm' hG
      · exact (key m' m τ' τ hle hm hG.symm).symm
    subst hmm
    have hττ : τ = τ' := Subtype.ext (mul_left_cancel hG)
    rw [hττ]
  · -- every element is `φ^m τ` with `m < n`
    intro d _
    obtain ⟨m, τ, hτ, hd⟩ := (hgen d).mp d.2
    have hτ' : (φ ^ residueDegree I φ I) ^ (m / residueDegree I φ I) * τ ∈ I :=
      I.mul_mem (pow_mem hn _) hτ
    refine ⟨⟨m % residueDegree I φ I, ⟨_, hτ'⟩⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr (Nat.mod_lt m (residueDegree_pos I φ I)), Finset.mem_univ _⟩,
      Subtype.ext ?_⟩
    show φ ^ (m % residueDegree I φ I) *
      ((φ ^ residueDegree I φ I) ^ (m / residueDegree I φ I) * τ) = d
    rw [hd, ← mul_assoc, ← pow_mul, ← pow_add, Nat.mod_add_div]
  · intro a _
    rw [one_mul]

/-- The number of elements of `H` in a subgroup, as a sum over the subgroup. -/
theorem card_subgroupOf_eq_cosetSum (D : Subgroup G) :
    (Nat.card (D.subgroupOf H) : ℂ) = cosetSum (extendByZero H fun _ => 1) D 1 := by
  have h := cosetSum_extendByZero_coe H (fun _ => (1 : ℂ)) (I := D) (I' := D.subgroupOf H)
    (fun _ => Subgroup.mem_subgroupOf) 1
  rw [Subgroup.coe_one] at h
  rw [h, cosetSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

/-- **The residue degree is an index**: if `D` is the union of the cosets `φ^m I`, then
`|H ∩ D| f = |H ∩ I| n`, with `n` the order of `φ` modulo `I`. -/
theorem card_subgroupOf_mul_residueDegree {I D : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ) :
    Nat.card (D.subgroupOf H) * residueDegree I φ H =
      Nat.card (I.subgroupOf H) * residueDegree I φ I := by
  obtain ⟨τ₀, hτ₀, hmem⟩ := cosetMeets_residueDegree I φ H
  -- `f` divides `n`: the coset `φ^n I = I` meets `H`
  obtain ⟨r, hr⟩ : residueDegree I φ H ∣ residueDegree I φ I :=
    (cosetMeets_iff_dvd hφ).mp ⟨(φ ^ residueDegree I φ I)⁻¹,
      I.inv_mem (pow_residueDegree_self_mem I φ), by
        rw [mul_inv_cancel]
        exact H.one_mem⟩
  have hsum : (Nat.card (D.subgroupOf H) : ℂ) = (r : ℂ) * (Nat.card (I.subgroupOf H) : ℂ) := by
    rw [card_subgroupOf_eq_cosetSum, cosetSum_one_eq_sum_range _ hφ hgen, hr,
      ← sum_range_mul_ite_dvd (residueDegree_pos I φ H) r]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [cosetSum_extendByZero H (fun _ => (1 : ℂ)) hφ (I' := I.subgroupOf H)
      (fun _ => Subgroup.mem_subgroupOf) (φ' := ⟨_, hmem⟩) hτ₀ rfl m]
    split_ifs
    · rw [cosetSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Nat.card_eq_fintype_card]
    · rfl
  have hnat : Nat.card (D.subgroupOf H) = r * Nat.card (I.subgroupOf H) := by
    exact_mod_cast hsum
  rw [hnat, hr]
  ring

/-- The group generated by `I` and `φ` has `n |I|` elements. -/
theorem card_eq_card_mul_residueDegree {I D : Subgroup G} {φ : G}
    (hφ : φ ∈ Subgroup.normalizer (I : Set G))
    (hgen : ∀ d : G, d ∈ D ↔ ∃ m : ℕ, ∃ τ ∈ I, d = φ ^ m * τ) :
    Nat.card D = residueDegree I φ I * Nat.card I := by
  have hsum : (Nat.card D : ℂ) = (residueDegree I φ I : ℂ) * (Nat.card I : ℂ) := by
    have h1 : (Nat.card D : ℂ) = cosetSum (fun _ => 1) D 1 := by
      rw [cosetSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Nat.card_eq_fintype_card]
    rw [h1, cosetSum_one_eq_sum_range _ hφ hgen]
    simp only [cosetSum, Finset.sum_const, Finset.card_univ, Finset.card_range, nsmul_eq_mul,
      mul_one, Nat.card_eq_fintype_card]
  exact_mod_cast hsum

end Induction

end GaloisForLFunctions
