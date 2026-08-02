import GaloisForLFunctions.HTGeometry.UniformJetPolyMixed

/-!
# A presentation with a nonvanishing residue

The dominant class of a presentation is a sum of residues, and nothing so far forbids it from
vanishing: two monomials of the same `Γ`-power, the same argument exponent and the same `log`-degree
can cancel at leading order.

Grouping the monomials the other way removes the possibility.  Each `Γ`-power carries a whole jet
polynomial, which has a nonzero residue by the dichotomy, and distinct `Γ`-powers cannot tie.  So a
presentation of a nonzero element has a nonzero residue — eq. (3) with the nonvanishing intact.

Vanishing coefficients and empty monomial ranges contribute nothing, so they can be pruned; what is
left is the hypothesis that some coefficient is nonzero.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Padding preserves distinctness of exponent vectors. -/
theorem padExp_injective {ι : Type*} {Kf K : ℕ} (hK : Kf ≤ K) {E : ι → Fin (Kf + 1) → ℕ}
    (hE : Function.Injective E) :
    Function.Injective (fun x : ι => fun i : Fin (K + 1) => padExp Kf (E x) (i : ℕ)) := by
  intro x y hxy
  refine hE ?_
  funext i
  have hi : (i : ℕ) < K + 1 := lt_of_lt_of_le i.isLt (by omega)
  have := congrFun hxy ⟨(i : ℕ), hi⟩
  simp only [padExp, dif_pos i.isLt] at this
  simpa using this

/-- **A family separated by Gamma exponent and log degree, with arbitrary argument exponents.** -/
theorem exists_tubeLimit_distinctKeyZ_residue {M : ℝ} (hM : 0 < M) {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (F : ι → ℝ → ℝ → ℂ) (k A e : ι → ℤ) (c : ι → ℂ)
    (hsep : ∀ α β : ι, k α = k β → e α = e β → α = β)
    (hlim : ∀ γ, TubeLimit M (fun σ t => F γ σ t / gammaShapeZ σ (k γ) (A γ) (e γ) t) (c γ)) :
    ∃ β : ι, TubeLimit M
      (fun σ t => (∑ γ : ι, F γ σ t) / gammaShapeZ σ (k β) (A β) (e β) t) (c β) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shapeZ_index_fintype k A e
  refine ⟨β, ?_⟩
  have hclass := tubeLimit_sum_div_dominant_class_fintype hM F k A e c β hlim hβ
  have hfilter : (Finset.univ.filter
      (fun γ : ι => k γ = k β ∧ A γ = A β ∧ e γ = e β)) = {β} := by
    refine Finset.ext fun γ => ?_
    constructor
    · intro hγ
      obtain ⟨h1, -, h3⟩ := Finset.mem_filter.mp hγ |>.2
      exact Finset.mem_singleton.mpr (hsep γ β h1 h3)
    · intro hγ
      rw [Finset.mem_singleton] at hγ
      subst hγ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ γ, rfl, rfl, rfl⟩
  rw [hfilter, Finset.sum_singleton] at hclass
  exact hclass

/-- **A presentation has a nonzero residue, uniformly on a tube.**  Each `Γ`-power carries a jet
polynomial whose residue is nonzero by the dichotomy, and distinct `Γ`-powers cannot tie. -/
theorem exists_tubeLimit_gammaPresentation_residue_nonzero {M : ℝ} (hM : 0 < M) {J : Type*}
    [Fintype J] [DecidableEq J] [Nonempty J] (ι : J → Type*) [∀ j, Fintype (ι j)]
    [∀ j, DecidableEq (ι j)] [∀ j, Nonempty (ι j)] (Kf : J → ℕ) (K d : ℕ) (hK : ∀ j, Kf j ≤ K)
    (u : J → ℕ) (huinj : Function.Injective u)
    (a : ∀ j : J, ι j → Polynomial ℂ) (E : ∀ j : J, ι j → Fin (Kf j + 1) → ℕ)
    (hdeg : ∀ j α, (a j α).natDegree ≤ d) (ha : ∀ j α, a j α ≠ 0)
    (hEinj : ∀ j, Function.Injective (E j)) :
    ∃ (k A e : ℤ) (c : ℂ), c ≠ 0 ∧
      TubeLimit M (fun σ t => (∑ j : J, gammaLine σ t ^ u j
          * (∑ α : ι j, (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i))
        / gammaShapeZ σ k A e t) c := by
  classical
  -- the residue of the jet polynomial carried by each Gamma power
  have hgroup : ∀ j : J, ∃ (p e : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      (∑ α : ι j, ((a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ padExp (Kf j) (E j α) (i : ℕ))
      / gammaShapeZ σ 0 (-(p : ℤ)) (e : ℤ) t) c := by
    intro j
    exact exists_tubeLimit_jetPoly_mixed_residue hM K d (a j)
      (fun α => fun i : Fin (K + 1) => padExp (Kf j) (E j α) (i : ℕ))
      (hdeg j) (padExp_injective (hK j) (hEinj j)) (ha j)
  choose p e c hc hlim using hgroup
  -- each Gamma power, with the argument normalization undone
  have hterm : ∀ j : J, TubeLimit M (fun σ t =>
      (gammaLine σ t ^ u j
        * ∑ α : ι j, (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
          * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i)
      / gammaShapeZ σ (u j : ℤ) (-(p j : ℤ) + (d : ℤ)) ((e j : ℤ)) t) (c j) := by
    intro j
    have hx := ((hlim j).mul_gammaPow (u j)).mul_pow_arg d
    refine hx.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      rw [h0] at him
      simp only [Complex.zero_im] at him
      linarith
    refine congrArg (fun w => w / gammaShapeZ σ (u j : ℤ) (-(p j : ℤ) + (d : ℤ))
      ((e j : ℤ)) t) ?_
    have key : ∀ α : ι j,
        ((a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin (K + 1), iteratedDeriv (i : ℕ) Complex.digamma
              ((σ : ℂ) + (t : ℂ) * Complex.I) ^ padExp (Kf j) (E j α) (i : ℕ)
        = ((a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i)
          / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d := by
      intro α
      rw [← prod_jets_pad (hK j) (E j α) ((σ : ℂ) + (t : ℂ) * Complex.I)]
      ring
    rw [Finset.sum_congr rfl fun α _ => key α, ← Finset.sum_div]
    field_simp
  -- distinct Gamma powers cannot tie
  obtain ⟨β, hβ⟩ := exists_tubeLimit_distinctKeyZ_residue hM
    (fun j σ t => gammaLine σ t ^ u j
      * ∑ α : ι j, (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i)
    (fun j => (u j : ℤ)) (fun j => -(p j : ℤ) + (d : ℤ)) (fun j => (e j : ℤ)) c
    (fun α γ hkey _ => huinj (by exact_mod_cast hkey)) hterm
  exact ⟨(u β : ℤ), -(p β : ℤ) + (d : ℤ), (e β : ℤ), c β, hc β, hβ⟩

/-- **A presentation with vanishing coefficients still has a nonzero residue.**  The terms with zero
coefficient, and the `Γ`-powers all of whose coefficients vanish, contribute nothing; pruning them
leaves a presentation to which the dichotomy applies. -/
theorem exists_tubeLimit_gammaPresentation_residue_prune {M : ℝ} (hM : 0 < M) {N : ℕ}
    (Mm : Fin N → ℕ) (Kf : Fin N → ℕ) (K d : ℕ) (hK : ∀ j, Kf j ≤ K) (u : Fin N → ℕ)
    (huinj : Function.Injective u) (a : ∀ j : Fin N, Fin (Mm j) → Polynomial ℂ)
    (E : ∀ j : Fin N, Fin (Mm j) → Fin (Kf j + 1) → ℕ)
    (hdeg : ∀ j α, (a j α).natDegree ≤ d) (hEinj : ∀ j, Function.Injective (E j))
    (hne : ∃ (j : Fin N) (α : Fin (Mm j)), a j α ≠ 0) :
    ∃ (k A e : ℤ) (c : ℂ), c ≠ 0 ∧
      TubeLimit M (fun σ t => (∑ j : Fin N, gammaLine σ t ^ u j
          * (∑ α : Fin (Mm j), (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
                ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i))
        / gammaShapeZ σ k A e t) c := by
  classical
  obtain ⟨j₀, α₀, hα₀⟩ := hne
  -- the surviving Gamma powers, and the surviving coefficients of each
  set J : Type := {j : Fin N // ∃ α : Fin (Mm j), a j α ≠ 0} with hJ
  set ι : J → Type := fun j => {α : Fin (Mm j.val) // a j.val α ≠ 0} with hι
  haveI : Nonempty J := ⟨⟨j₀, ⟨α₀, hα₀⟩⟩⟩
  haveI : ∀ j : J, Nonempty (ι j) := by
    intro j
    obtain ⟨α, hα⟩ := j.2
    exact ⟨⟨α, hα⟩⟩
  haveI : Fintype J := Fintype.ofFinite _
  haveI : ∀ j : J, Fintype (ι j) := fun j => Fintype.ofFinite _
  haveI : DecidableEq J := Classical.decEq _
  haveI : ∀ j : J, DecidableEq (ι j) := fun j => Classical.decEq _
  obtain ⟨k, A, e, c, hc, hlim⟩ := exists_tubeLimit_gammaPresentation_residue_nonzero hM ι
    (fun j => Kf j.val) K d (fun j => hK j.val) (fun j => u j.val)
    (fun x y hxy => Subtype.ext (huinj hxy))
    (fun j α => a j.val α.val) (fun j α => E j.val α.val)
    (fun j α => hdeg _ _) (fun j α => α.2)
    (fun j x y hxy => Subtype.ext (hEinj j.val hxy))
  refine ⟨k, A, e, c, hc, ?_⟩
  refine hlim.congr (T₀ := 0) fun σ t hσ hσM ht => ?_
  refine congrArg (fun w => w / gammaShapeZ σ k A e t) ?_
  -- the pruned terms vanish
  set f : ∀ j : Fin N, Fin (Mm j) → ℂ := fun j α =>
    (a j α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (Kf j + 1), iteratedDeriv (i : ℕ) Complex.digamma
          ((σ : ℂ) + (t : ℂ) * Complex.I) ^ E j α i with hf
  have hfzero : ∀ (j : Fin N) (α : Fin (Mm j)), a j α = 0 → f j α = 0 := by
    intro j α hja
    rw [hf]
    simp [hja]
  have hinner : ∀ j : Fin N, ∑ α ∈ Finset.univ.filter (fun α : Fin (Mm j) => a j α ≠ 0), f j α
      = ∑ α : Fin (Mm j), f j α := by
    intro j
    refine Finset.sum_subset (Finset.filter_subset _ _) fun α _ hα => ?_
    have : a j α = 0 := by
      by_contra hne'
      exact hα (Finset.mem_filter.mpr ⟨Finset.mem_univ α, hne'⟩)
    exact hfzero j α this
  have hstep : ∀ j : J, ∑ α : ι j, f j.val α.val = ∑ α : Fin (Mm j.val), f j.val α := by
    intro j
    rw [← hinner j.val]
    exact (Finset.sum_subtype (p := fun α : Fin (Mm j.val) => a j.val α ≠ 0)
      (s := Finset.univ.filter (fun α : Fin (Mm j.val) => a j.val α ≠ 0))
      (fun α => by simp [Finset.mem_filter]) (f j.val)).symm
  have houter : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∃ α : Fin (Mm j), a j α ≠ 0),
      gammaLine σ t ^ u j * ∑ α : Fin (Mm j), f j α
      = ∑ j : Fin N, gammaLine σ t ^ u j * ∑ α : Fin (Mm j), f j α := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
    have hall : ∀ α : Fin (Mm j), a j α = 0 := by
      intro α
      by_contra hne'
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨α, hne'⟩⟩)
    have : ∑ α : Fin (Mm j), f j α = 0 :=
      Finset.sum_eq_zero fun α _ => hfzero j α (hall α)
    rw [this, mul_zero]
  calc ∑ j : J, gammaLine σ t ^ u j.val * ∑ α : ι j, f j.val α.val
      = ∑ j : J, gammaLine σ t ^ u j.val * ∑ α : Fin (Mm j.val), f j.val α :=
        Finset.sum_congr rfl fun j _ => by rw [hstep j]
    _ = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∃ α : Fin (Mm j), a j α ≠ 0),
          gammaLine σ t ^ u j * ∑ α : Fin (Mm j), f j α :=
        (Finset.sum_subtype (p := fun j : Fin N => ∃ α : Fin (Mm j), a j α ≠ 0)
          (s := Finset.univ.filter (fun j : Fin N => ∃ α : Fin (Mm j), a j α ≠ 0))
          (fun j => by simp [Finset.mem_filter])
          (fun j => gammaLine σ t ^ u j * ∑ α : Fin (Mm j), f j α)).symm
    _ = ∑ j : Fin N, gammaLine σ t ^ u j * ∑ α : Fin (Mm j), f j α := houter

end

end GaloisForLFunctions.HTGeometry
