import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexOfAFiniteExponentialSum
import GaloisForLFunctions.HeckeKreinToeplitz.AllButFinitelyManyPrimesSeeTheWholeIndex

/-!
# Index carriers of finite spectra

A Hermitian finite exponential sum `k = Σ_{χ ∈ S} a_χ χ` on a group has the index of its spectral
matrix, and HKT reads it on *some* finite family (Dedekind–Artin). This file names the family. A
family **carries** `S` when the evaluation matrix `(χ(x_b))` has full row rank; then the Gram matrix
of `k` on it has exactly `κ(k)` negative squares (`hermNegIndex_gram_expSum_eq_of_carries`).

* **One element** (`window_carries`). If `χ ↦ χ(g)` is injective on `S`, the window
  `g⁰, …, g^{n−1}`, `n ≥ |S|`, carries `S`: its evaluation matrix contains a Vandermonde matrix,
  and the Lagrange basis interpolates every coordinate vector.
* **Two commuting elements** (`box_carries`). If `χ ↦ (χ(g), χ(h))` is injective on `S`, the box
  `gⁱhʲ`, `i, j < n`, carries `S`. A generic linear form `χ(g) + tχ(h)` separates the points, and
  its powers expand binomially into the box.
* **The arithmetic instance** (`twoPrime_box_carries`, `prime_window_carries`). On `ℚ_{>0}` the
  characters `u ↦ u^{ρ−½}` are separated by two primes `p ≠ q`, since a pair of exponents aliases
  at most at one prime; so the box `pⁱqʲ`, `i, j < |S|`, reads the index of every Hermitian
  exponential sum of zero characters, and the window `p⁰, …, p^{|S|−1}` does whenever no two of the
  exponents alias at `p`.

These are the finite sections of the Hasse principle: the section size is the size of the spectrum,
with no separation margin and no hypothesis on the weights.
-/

open Complex Finset Matrix Polynomial
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

variable {G : Type*} [Group G]

/-- A family **carries** a finite set of characters when its evaluation matrix has full row rank. -/
def Carries (S : Finset (G →* ℂ)) {ι : Type*} [Fintype ι] (x : ι → G) : Prop :=
  LinearMap.range (evalMat S x).mulVecLin = ⊤

/-- **A carrying family reads the index.** -/
theorem hermNegIndex_gram_expSum_eq_of_carries {S : Finset (G →* ℂ)}
    (hS : ∀ χ ∈ S, reflectChar χ ∈ S) (a : (G →* ℂ) → ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {x : ι → G} (hx : Carries S x) :
    (hermNegIndex (gram (expSum S a) x) : ℕ∞) = negIndex (expSum S a) := by
  refine le_antisymm (hermNegIndex_gram_le_negIndex _ x) ?_
  rw [negIndex_expSum_eq hS]
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective _ hx
  refine Nat.cast_le.mpr (hermNegIndex_le_of_hermQuad_eq _ _ R fun y => ?_)
  rw [gram_expSum hS, hermQuad_rect_conjugate]
  congr 1
  exact LinearMap.congr_fun hR y

/-! ### Interpolation -/

/-- **Lagrange.** For injective nodes `w` on a finite type `S` and `n ≥ |S|`, the vectors
`(w_χ^k)_χ`, `k < n`, span `S → ℂ`. -/
theorem span_pow_eq_top {S : Type*} [Fintype S] [DecidableEq S] {w : S → ℂ}
    (hw : Function.Injective w) {n : ℕ} (hn : Fintype.card S ≤ n) :
    Submodule.span ℂ (Set.range fun k : Fin n => fun χ => w χ ^ (k : ℕ)) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : v = ∑ χ₀ : S, v χ₀ • fun χ => if χ = χ₀ then (1 : ℂ) else 0 := by
    funext χ; simp [Finset.sum_apply]
  rw [hv]
  refine Submodule.sum_mem _ fun χ₀ _ => Submodule.smul_mem _ _ ?_
  set P := Lagrange.basis (univ : Finset S) w χ₀
  have hinj : Set.InjOn w (univ : Finset S) := fun a _ b _ h => hw h
  have hdeg : P.natDegree < n := by
    rw [Lagrange.natDegree_basis hinj (mem_univ _), card_univ]
    have : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨χ₀⟩
    omega
  have hδ : (fun χ => if χ = χ₀ then (1 : ℂ) else 0) =
      ∑ k : Fin n, P.coeff k • fun χ => w χ ^ (k : ℕ) := by
    funext χ
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun k => P.coeff k * w χ ^ k) n,
      ← Polynomial.eval_eq_sum_range' hdeg]
    by_cases h : χ = χ₀
    · rw [if_pos h, h, Lagrange.eval_basis_self hinj (mem_univ _)]
    · rw [if_neg h, Lagrange.eval_basis_of_ne (Ne.symm h) (mem_univ _)]
  rw [hδ]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem carries_iff_span {S : Finset (G →* ℂ)} {ι : Type*} [Fintype ι] (x : ι → G) :
    Carries S x ↔
      Submodule.span ℂ (Set.range fun b : ι => fun χ : S => (χ : G →* ℂ) (x b)) = ⊤ := by
  unfold Carries
  rw [Matrix.range_mulVecLin]
  rfl

/-- **One element carries a separated spectrum.** -/
theorem window_carries {S : Finset (G →* ℂ)} {g : G}
    (hg : Set.InjOn (fun χ : G →* ℂ => χ g) S) {n : ℕ} (hn : S.card ≤ n) :
    Carries S fun k : Fin n => g ^ (k : ℕ) := by
  classical
  rw [carries_iff_span]
  have hw : Function.Injective fun χ : S => (χ : G →* ℂ) g := fun a b h =>
    Subtype.ext (hg a.2 b.2 h)
  have := span_pow_eq_top hw (n := n) (by simpa using hn)
  simpa only [map_pow] using this

/-- **Two commuting elements carry a jointly separated spectrum.** -/
theorem box_carries {G : Type*} [CommGroup G] {S : Finset (G →* ℂ)} {g h : G}
    (hgh : Set.InjOn (fun χ : G →* ℂ => (χ g, χ h)) S) {n : ℕ} (hn : S.card ≤ n) :
    Carries S fun b : Fin n × Fin n => g ^ (b.1 : ℕ) * h ^ (b.2 : ℕ) := by
  classical
  rw [carries_iff_span]
  set W := Submodule.span ℂ
    (Set.range fun b : Fin n × Fin n => fun χ : S => (χ : G →* ℂ) (g ^ (b.1 : ℕ) * h ^ (b.2 : ℕ)))
  -- a separating linear form `χ(g) + t χ(h)`
  set bad : Finset ℂ := (univ : Finset (S × S)).image fun p =>
    -(((p.1 : G →* ℂ) g - (p.2 : G →* ℂ) g) / ((p.1 : G →* ℂ) h - (p.2 : G →* ℂ) h))
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset bad
  set w : S → ℂ := fun χ => (χ : G →* ℂ) g + t * (χ : G →* ℂ) h
  have hw : Function.Injective w := by
    intro χ χ' he
    by_contra hne
    have hne' : (χ : G →* ℂ) ≠ χ' := fun h' => hne (Subtype.ext h')
    by_cases hh : (χ : G →* ℂ) h = (χ' : G →* ℂ) h
    · have hg' : (χ : G →* ℂ) g = (χ' : G →* ℂ) g := by
        simp only [w, hh] at he; linear_combination he
      exact hne' (hgh χ.2 χ'.2 (Prod.ext hg' hh))
    · apply ht
      refine mem_image.mpr ⟨(χ, χ'), mem_univ _, ?_⟩
      have hd : (χ : G →* ℂ) h - (χ' : G →* ℂ) h ≠ 0 := sub_ne_zero.mpr hh
      simp only [w] at he
      rw [neg_div', div_eq_iff hd]
      linear_combination (-1 : ℂ) * he
  -- the powers of the linear form lie in the span of the box
  have hpow : ∀ k : Fin n, (fun χ : S => w χ ^ (k : ℕ)) ∈ W := fun k => by
    have hexp : (fun χ : S => w χ ^ (k : ℕ)) = ∑ i ∈ range ((k : ℕ) + 1),
        ((t ^ ((k : ℕ) - i) * ((k : ℕ).choose i : ℂ)) • fun χ : S =>
          (χ : G →* ℂ) (g ^ i * h ^ ((k : ℕ) - i))) := by
      funext χ
      simp only [w, add_pow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hexp]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
    exact ⟨(⟨i, lt_of_le_of_lt hik k.2⟩, ⟨(k : ℕ) - i, lt_of_le_of_lt (Nat.sub_le _ _) k.2⟩), rfl⟩
  refine eq_top_iff.mpr ?_
  rw [← span_pow_eq_top hw (n := n) (by simpa using hn)]
  exact Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact hpow k)

/-! ### The arithmetic instance on `ℚ_{>0}` -/

/-- **Two primes carry every finite spectrum of zero characters.** For distinct primes `p, q` and a
finite set `S` of characters `u ↦ u^{ρ−½}`, the box `pⁱqʲ`, `i, j < n`, `n ≥ |S|`, carries `S`. -/
theorem twoPrime_box_carries {S : Finset (HeckeLattice →* ℂ)} (hS : ∀ χ ∈ S, ∃ ρ, χ = zeroChar ρ)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {n : ℕ} (hn : S.card ≤ n) :
    Carries S fun b : Fin n × Fin n => primeElt hp ^ (b.1 : ℕ) * primeElt hq ^ (b.2 : ℕ) := by
  refine box_carries (fun χ hχ χ' hχ' h => ?_) hn
  obtain ⟨ρ, rfl⟩ := hS χ hχ
  obtain ⟨ρ', rfl⟩ := hS χ' hχ'
  by_contra hne
  have hρ : ρ ≠ ρ' := fun h' => hne (by rw [h'])
  exact hpq (eq_of_alias_of_alias hρ hp hq (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- **One prime carries a spectrum it does not alias.** -/
theorem prime_window_carries {S : Finset (HeckeLattice →* ℂ)} {p : ℕ} (hp : p.Prime)
    (hinj : Set.InjOn (fun χ : HeckeLattice →* ℂ => χ (primeElt hp)) S) {n : ℕ}
    (hn : S.card ≤ n) : Carries S fun k : Fin n => primeElt hp ^ (k : ℕ) :=
  window_carries hinj hn

/-- **The index of a finite exponential sum of zero characters is read on a two-prime box** of
side `|S|`. -/
theorem hermNegIndex_twoPrime_box_eq {S : Finset (HeckeLattice →* ℂ)}
    (hS : ∀ χ ∈ S, reflectChar χ ∈ S) (hSz : ∀ χ ∈ S, ∃ ρ, χ = zeroChar ρ)
    (a : (HeckeLattice →* ℂ) → ℂ) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (hermNegIndex (gram (expSum S a)
      fun b : Fin S.card × Fin S.card => primeElt hp ^ (b.1 : ℕ) * primeElt hq ^ (b.2 : ℕ)) : ℕ∞) =
      negIndex (expSum S a) :=
  hermNegIndex_gram_expSum_eq_of_carries hS a (twoPrime_box_carries hSz hp hq hpq le_rfl)

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
