import Mathlib

/-!
# The series of a multiplicative function is its Euler product

Let `f : ι → V → R` assign to every "prime" `i` a local series over exponent data `v ∈ V` with
`f i 0 = 1`. A finitely supported exponent vector `g : ι →₀ V` has the multiplicative term
`F(g) = ∏_{i ∈ supp g} f i (g i)` (`eulerTerm`). If every local series converges absolutely and
the excess masses `Σ_v ‖f i v‖ − 1` are summable over `i`, then the terms are absolutely summable
and

`Σ_g F(g) = ∏_i Σ_v f i v`   (`hasProd_tsum_eulerTerm`).

The exponent data are arbitrary, so this covers series in several ideal variables at once (one
coordinate of `V` per variable); the completely multiplicative geometric case is
`HTGeometry.hasProd_inv_one_sub_nome`.

The proof: over a finite set `S` of primes the vectors supported in `S` are the functions
`S → V`, and the product of finitely many absolutely convergent series is the series of the
products (`hasSum_pi_prod`); the partial masses are bounded by `exp Σ_i (‖f i‖₁ − 1)`, and
dominated convergence lets `S` exhaust `ι`.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.FamilyContinuationTheory

/-! ### Finitely many series -/

section FinitePi

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {W : Type*}

private theorem hasSum_pi_prod_fin :
    ∀ (n : ℕ) (φ : Fin n → W → R) (s : Fin n → R), (∀ k, HasSum (φ k) (s k)) →
      (∀ k, Summable fun w => ‖φ k w‖) →
      HasSum (fun h : Fin n → W => ∏ k, φ k (h k)) (∏ k, s k) ∧
        Summable (fun h : Fin n → W => ‖∏ k, φ k (h k)‖) := by
  intro n
  induction n with
  | zero =>
    intro φ s _ _
    haveI : Unique (Fin 0 → W) := Pi.uniqueOfIsEmpty _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
    exact ⟨hasSum_single default fun b hb => absurd (Subsingleton.elim b default) hb,
      ⟨1, hasSum_single default fun b hb => absurd (Subsingleton.elim b default) hb⟩⟩
  | succ n ih =>
    intro φ s hs hn
    obtain ⟨ihs, ihn⟩ := ih (fun k => φ k.succ) (fun k => s k.succ) (fun k => hs k.succ)
      (fun k => hn k.succ)
    have hpair : Summable (fun x : W × (Fin n → W) => φ 0 x.1 * ∏ k : Fin n, φ k.succ (x.2 k)) :=
      summable_mul_of_summable_norm (f := φ 0) (g := fun h : Fin n → W => ∏ k, φ k.succ (h k))
        (hn 0) ihn
    have hmul := HasSum.mul (f := φ 0) (g := fun h : Fin n → W => ∏ k, φ k.succ (h k)) (hs 0)
      ihs hpair
    have hsplit : ∀ h : Fin (n + 1) → W, ∏ k, φ k (h k) = φ 0 (h 0) * ∏ k : Fin n, φ k.succ (h k.succ) :=
      fun h => Fin.prod_univ_succ _
    constructor
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => W).hasSum_iff, Fin.prod_univ_succ]
      refine hmul.congr_fun fun x => ?_
      rw [Function.comp_apply, hsplit]
      simp [Fin.consEquiv]
    · rw [← (Fin.consEquiv fun _ : Fin (n + 1) => W).summable_iff]
      refine hpair.norm.congr fun x => ?_
      rw [Function.comp_apply, hsplit]
      simp [Fin.consEquiv]

/-- **A finite product of absolutely convergent series** is the absolutely convergent series of
the products over all choices of terms. -/
theorem hasSum_pi_prod {κ : Type*} [Fintype κ] (φ : κ → W → R) (s : κ → R)
    (hs : ∀ k, HasSum (φ k) (s k)) (hn : ∀ k, Summable fun w => ‖φ k w‖) :
    HasSum (fun h : κ → W => ∏ k, φ k (h k)) (∏ k, s k) ∧
      Summable (fun h : κ → W => ‖∏ k, φ k (h k)‖) := by
  classical
  let e := Fintype.equivFin κ
  let pe : (κ → W) ≃ (Fin (Fintype.card κ) → W) := Equiv.piCongrLeft (fun _ => W) e
  obtain ⟨hfin, hnorm⟩ := hasSum_pi_prod_fin (Fintype.card κ) (fun j => φ (e.symm j))
    (fun j => s (e.symm j)) (fun j => hs _) (fun j => hn _)
  have hval : ∏ j, s (e.symm j) = ∏ k, s k :=
    Fintype.prod_equiv e.symm _ _ (fun _ => rfl)
  have hterm : ∀ h : Fin (Fintype.card κ) → W,
      ∏ j, φ (e.symm j) (h j) = ∏ k, φ k ((pe.symm h) k) := by
    intro h
    exact Fintype.prod_equiv e.symm _ _ (fun j => by simp [pe])
  rw [hval] at hfin
  refine ⟨(Equiv.hasSum_iff pe.symm).mp ?_, (Equiv.summable_iff pe.symm).mp ?_⟩
  · exact hfin.congr_fun fun h => (hterm h).symm
  · exact hnorm.congr fun h => by rw [Function.comp_apply, ← hterm h]

end FinitePi

/-! ### The Euler product -/

variable {ι V : Type*} [Zero V]

/-- The multiplicative term `F(g) = ∏_{i ∈ supp g} f i (g i)` of an exponent vector. -/
def eulerTerm (f : ι → V → ℂ) (g : ι →₀ V) : ℂ := g.prod f

/-- The exponent vectors supported in a finite set are the functions on it. -/
def supportedEmbedding (S : Finset ι) (h : S → V) : ι →₀ V :=
  Finsupp.embDomain (Function.Embedding.subtype (· ∈ S)) (Finsupp.equivFunOnFinite.symm h)

theorem supportedEmbedding_injective (S : Finset ι) :
    Function.Injective (supportedEmbedding (V := V) S) := fun h₁ h₂ hh =>
  Finsupp.equivFunOnFinite.symm.injective (Finsupp.embDomain_injective _ hh)

theorem support_supportedEmbedding_subset (S : Finset ι) (h : S → V) :
    (supportedEmbedding S h).support ⊆ S := by
  classical
  intro i hi
  rw [supportedEmbedding, Finsupp.support_embDomain, Finset.mem_map] at hi
  obtain ⟨a, -, rfl⟩ := hi
  exact a.2

theorem mem_range_supportedEmbedding (S : Finset ι) (g : ι →₀ V) (hg : g.support ⊆ S) :
    g ∈ Set.range (supportedEmbedding S) := by
  classical
  refine ⟨fun a => g a, ?_⟩
  ext i
  by_cases hi : i ∈ S
  · have := Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∈ S))
      (Finsupp.equivFunOnFinite.symm fun a : S => g a) ⟨i, hi⟩
    simpa [supportedEmbedding] using this
  · rw [supportedEmbedding, Finsupp.embDomain_notin_range]
    · exact (Finsupp.notMem_support_iff.mp fun h => hi (hg h)).symm
    · rintro ⟨a, rfl⟩
      exact hi a.2

theorem eulerTerm_supportedEmbedding (f : ι → V → ℂ) (hf0 : ∀ i, f i 0 = 1) (S : Finset ι)
    (h : S → V) : eulerTerm f (supportedEmbedding S h) = ∏ a : S, f a (h a) := by
  classical
  rw [eulerTerm, supportedEmbedding, Finsupp.prod_embDomain, Finsupp.prod_fintype]
  · rfl
  · intro a
    exact hf0 a

/-- **The finite Euler product.** -/
theorem hasSum_indicator_eulerTerm (f : ι → V → ℂ) (hf0 : ∀ i, f i 0 = 1)
    (hs : ∀ i, Summable fun v => ‖f i v‖) (S : Finset ι) :
    HasSum (Set.indicator {g : ι →₀ V | g.support ⊆ S} (eulerTerm f))
      (∏ i ∈ S, ∑' v, f i v) := by
  classical
  have hpi := (hasSum_pi_prod (fun a : S => f a) (fun a : S => ∑' v, f a v)
    (fun a => (hs a).of_norm.hasSum) (fun a => hs a)).1
  have hval : ∏ a : S, ∑' v, f a v = ∏ i ∈ S, ∑' v, f i v :=
    (Finset.prod_subtype S (fun _ => Iff.rfl) (fun i => ∑' v, f i v)).symm
  rw [hval] at hpi
  refine ((supportedEmbedding_injective S).hasSum_iff ?_).mp ?_
  · intro g hg
    rw [Set.indicator_of_notMem]
    exact fun hmem => hg (mem_range_supportedEmbedding S g hmem)
  · refine hpi.congr_fun fun h => ?_
    rw [Function.comp_apply, Set.indicator_of_mem (support_supportedEmbedding_subset S h),
      eulerTerm_supportedEmbedding f hf0]

/-- The local masses `Σ_v ‖f i v‖ ≥ 1`. -/
theorem one_le_tsum_norm (f : ι → V → ℂ) (hf0 : ∀ i, f i 0 = 1)
    (hs : ∀ i, Summable fun v => ‖f i v‖) (i : ι) : 1 ≤ ∑' v, ‖f i v‖ := by
  have h := (hs i).le_tsum 0 (fun v _ => norm_nonneg _)
  rwa [hf0, norm_one] at h

/-- **Absolute summability.** -/
theorem summable_norm_eulerTerm (f : ι → V → ℂ) (hf0 : ∀ i, f i 0 = 1)
    (hs : ∀ i, Summable fun v => ‖f i v‖)
    (hb : Summable fun i => ∑' v, ‖f i v‖ - 1) :
    Summable fun g : ι →₀ V => ‖eulerTerm f g‖ := by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' i, (∑' v, ‖f i v‖ - 1)))
    (fun g => norm_nonneg _) fun T => ?_
  let S : Finset ι := T.sup Finsupp.support
  -- the norms of the supported terms are the products of the local norms
  have hnorm : HasSum (Set.indicator {g : ι →₀ V | g.support ⊆ S} fun g => ‖eulerTerm f g‖)
      (∏ i ∈ S, ∑' v, ‖f i v‖) := by
    have hpi := (hasSum_pi_prod (R := ℝ) (fun a : S => fun v => ‖f a v‖)
      (fun a : S => ∑' v, ‖f a v‖) (fun a => (hs a).hasSum)
      (fun a => by simpa using hs a)).1
    have hval : ∏ a : S, ∑' v, ‖f a v‖ = ∏ i ∈ S, ∑' v, ‖f i v‖ :=
      (Finset.prod_subtype S (fun _ => Iff.rfl) (fun i => ∑' v, ‖f i v‖)).symm
    rw [hval] at hpi
    refine ((supportedEmbedding_injective S).hasSum_iff ?_).mp ?_
    · intro g hg
      rw [Set.indicator_of_notMem]
      exact fun hmem => hg (mem_range_supportedEmbedding S g hmem)
    · refine hpi.congr_fun fun h => ?_
      rw [Function.comp_apply, Set.indicator_of_mem (support_supportedEmbedding_subset S h),
        eulerTerm_supportedEmbedding f hf0, norm_prod]
  have hT : ∑ g ∈ T, ‖eulerTerm f g‖ ≤ ∏ i ∈ S, ∑' v, ‖f i v‖ := by
    have hle := sum_le_hasSum T (fun g _ => Set.indicator_nonneg (fun g _ => norm_nonneg _) g) hnorm
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun g hg => ?_)) hle
    rw [Set.indicator_of_mem]
    exact Finset.le_sup (f := Finsupp.support) hg
  have hprod : ∏ i ∈ S, ∑' v, ‖f i v‖ ≤ Real.exp (∑ i ∈ S, (∑' v, ‖f i v‖ - 1)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun i _ => le_trans zero_le_one
      (one_le_tsum_norm f hf0 hs i)) fun i _ => ?_
    have := Real.add_one_le_exp (∑' v, ‖f i v‖ - 1)
    linarith
  have hsum : ∑ i ∈ S, (∑' v, ‖f i v‖ - 1) ≤ ∑' i, (∑' v, ‖f i v‖ - 1) :=
    hb.sum_le_tsum S fun i _ => sub_nonneg.mpr (one_le_tsum_norm f hf0 hs i)
  exact hT.trans (hprod.trans (Real.exp_le_exp.mpr hsum))

/-- **The Euler product.** If the local series converge absolutely with summable excess masses,
the multiplicative series over all exponent vectors is the product of the local sums. -/
theorem hasProd_tsum_eulerTerm (f : ι → V → ℂ) (hf0 : ∀ i, f i 0 = 1)
    (hs : ∀ i, Summable fun v => ‖f i v‖)
    (hb : Summable fun i => ∑' v, ‖f i v‖ - 1) :
    HasProd (fun i => ∑' v, f i v) (∑' g : ι →₀ V, eulerTerm f g) := by
  classical
  have hbound := summable_norm_eulerTerm f hf0 hs hb
  have hpoint : ∀ g : ι →₀ V, Tendsto (fun S : Finset ι =>
      Set.indicator {g : ι →₀ V | g.support ⊆ S} (eulerTerm f) g) atTop (𝓝 (eulerTerm f g)) := by
    intro g
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop g.support] with S hS
    rw [Set.indicator_of_mem (show g ∈ {g : ι →₀ V | g.support ⊆ S} from hS)]
  have hdom : ∀ᶠ S : Finset ι in atTop, ∀ g : ι →₀ V,
      ‖Set.indicator {g : ι →₀ V | g.support ⊆ S} (eulerTerm f) g‖ ≤ ‖eulerTerm f g‖ := by
    refine Eventually.of_forall fun S g => ?_
    by_cases hg : g ∈ {g : ι →₀ V | g.support ⊆ S}
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg, norm_zero]
      exact norm_nonneg _
  have hlim := tendsto_tsum_of_dominated_convergence hbound hpoint hdom
  have hval : ∀ S : Finset ι,
      (∑' g, Set.indicator {g : ι →₀ V | g.support ⊆ S} (eulerTerm f) g) =
        ∏ i ∈ S, ∑' v, f i v := fun S => (hasSum_indicator_eulerTerm f hf0 hs S).tsum_eq
  rw [funext hval] at hlim
  exact hlim

end GaloisForLFunctions.FamilyContinuationTheory
