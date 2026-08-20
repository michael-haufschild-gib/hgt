import GaloisForLFunctions.HTGeometry.AllDepthBottomCharge
import GaloisForLFunctions.HTGeometry.AllDepthTelescope
import GaloisForLFunctions.HTGeometry.TripticOrbitalDivisorLinearity
import GaloisForLFunctions.HTGeometry.TripticLineFiniteness
import GaloisForLFunctions.HTGeometry.TripticSourceDivisorFinsupp

/-!
# Descending the pair-face signature one depth

For a pair `{i, j}` avoiding the distinguished direction `k`, the depth-`d` pair-face witness is the
`τ k`-difference of the depth-`(d−1)` one.  Hence the depth-`d` signature at `{i, j}` is the
`τ k`-displacement of the depth-`(d−1)` signature:

```text
S^(d)_(ij)(F)(p, ℓ) = R(p + τ k, ℓ) − R(p, ℓ),   R = R_2^(ij)(W^(d−1)_(ij) F).
```

So a vanishing depth-`d` signature makes `R` invariant under `τ k`.  Since `R` is invariant under
`H_(ij) = ℤ + ℤ τ i + ℤ τ j`, has only finitely many nonzero classes there, and `τ k` has infinite
order modulo `H_(ij)`, this forces `R = 0`: the depth-`(d−1)` signature vanishes too.

* `pairFaceWitnessFun_eq_shiftDiffFun`;
* `additiveOrbitalDivisorAt_comp_add`;
* **`additiveOrbitalDivisorAt_shiftDiffFun`** — the displacement formula.
-/

open Filter Set Topology
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The depth-`d` pair-face witness is the `τ k`-difference of the depth-`(d−1)` one.** -/
theorem pairFaceWitnessFun_eq_shiftDiffFun (τ : ι → ℂ) {i j k : ι} (hki : k ≠ i) (hkj : k ≠ j)
    (f : ℂ → ℂ) :
    pairFaceWitnessFun τ i j f =
      HTGeometry.shiftDiffFun (τ k)
        (HTGeometry.diffCube τ ((Finset.univ : Finset ι) \ {i, j, k}) f) := by
  classical
  have hdisj : Disjoint ({k} : Finset ι) ((Finset.univ : Finset ι) \ {i, j, k}) := by
    rw [Finset.disjoint_left]
    intro m hm hm'
    have hmk : m = k := by simpa using hm
    exact (Finset.mem_sdiff.mp hm').2 (by simp [hmk])
  have hunion : ({k} : Finset ι) ∪ ((Finset.univ : Finset ι) \ {i, j, k}) =
      (Finset.univ : Finset ι) \ {i, j} := by
    ext m
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_insert]
    constructor
    · rintro (rfl | hm)
      · rintro (h | h)
        · exact hki h
        · exact hkj h
      · intro h
        exact hm (h.imp id Or.inl)
    · intro hm
      by_cases hmk : m = k
      · exact Or.inl hmk
      · refine Or.inr ?_
        rintro (h | h | h)
        · exact hm (Or.inl h)
        · exact hm (Or.inr h)
        · exact hmk h
  rw [pairFaceWitnessFun, ← hunion, HTGeometry.diffCube_union τ hdisj,
    HTGeometry.diffCube_singleton]

/-- **The orbital divisor is translation covariant.** -/
theorem additiveOrbitalDivisorAt_comp_add (G : ℂ → ℂ) (σ c p : ℂ) (ℓ : ℤ) :
    additiveOrbitalDivisorAt (fun z => G (z + c)) σ p ℓ =
      additiveOrbitalDivisorAt G σ (p + c) ℓ := by
  rw [additiveOrbitalDivisorAt, additiveOrbitalDivisorAt]
  refine finsum_congr fun m => ?_
  have hfun : (fun w : ℂ => G (w + σ + c) - G (w + c)) =
      fun w : ℂ => (fun u : ℂ => G (u + σ) - G u) (w + c) := by
    funext w
    show G (w + σ + c) - G (w + c) = G (w + c + σ) - G (w + c)
    rw [show w + σ + c = w + c + σ from by ring]
  rw [hfun, laurentCoeff_comp_add (fun u : ℂ => G (u + σ) - G u) (p + (m : ℂ) * σ) c ℓ]
  congr 1
  ring

/-- **The signature of a `τ k`-difference is the `τ k`-displacement of the signature.** -/
theorem additiveOrbitalDivisorAt_shiftDiffFun {G : ℂ → ℂ} {σ c p : ℂ} {ℓ : ℤ}
    (hG : MeromorphicOn G (Set.univ : Set ℂ))
    (hs1 : {m : ℤ | laurentCoeff (fun w : ℂ => G (w + σ + c) - G (w + c))
      (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite)
    (hs2 : {m : ℤ | laurentCoeff (fun w : ℂ => G (w + σ) - G w) (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite) :
    additiveOrbitalDivisorAt (HTGeometry.shiftDiffFun c G) σ p ℓ =
      additiveOrbitalDivisorAt G σ (p + c) ℓ - additiveOrbitalDivisorAt G σ p ℓ := by
  have hshift : MeromorphicOn (fun z => G (z + c)) (Set.univ : Set ℂ) := by
    intro z _
    exact meromorphicAt_comp_add.mpr (hG (z + c) (Set.mem_univ _))
  have hsub := additiveOrbitalDivisorAt_sub (F := fun z => G (z + c)) (G := G)
    (σ := σ) (p := p) (ℓ := ℓ) hshift hG hs1 hs2
  show additiveOrbitalDivisorAt (fun z => G (z + c) - G z) σ p ℓ = _
  rw [hsub, additiveOrbitalDivisorAt_comp_add G σ c p ℓ]

/-! ## Finitely many nonzero classes -/

set_option maxHeartbeats 1000000 in
/-- **The depth-two orbital divisor has finitely many nonzero classes modulo the period group.** -/
theorem exists_finset_orbitalDivisor_classes {G : ℂ → ℂ} {τ σ : ℂ}
    (hG : MeromorphicOn G (Set.univ : Set ℂ)) (hper : PeriodicOneGerm G)
    {Cst : ℂ} (hmixed : MixedConstGerm G τ σ Cst)
    (hτ : 0 < τ.im) {ℓ : ℤ} (hℓ : ℓ < 0) :
    ∃ S : Finset ℂ, ∀ p, additiveOrbitalDivisorAt G σ p ℓ ≠ 0 →
      ∃ s ∈ S, p - s ∈ tripticPeriodGroup τ σ := by
  classical
  set U : ℂ → ℂ := fun w => G (w + σ) - G w with hU
  have hUmero : MeromorphicOn U (Set.univ : Set ℂ) := fun y _ =>
    (meromorphicAt_comp_add.mpr (hG (y + σ) (Set.mem_univ _))).sub (hG y (Set.mem_univ y))
  have hone : ∀ (k : ℤ), k < 0 → ∀ z : ℂ, laurentCoeff U (z + 1) k = laurentCoeff U z k :=
    fun k _ z => laurentCoeff_boundary_periodic_one hG hper k z
  have htau : ∀ (k : ℤ), k < 0 → ∀ z : ℂ, laurentCoeff U (z + τ) k = laurentCoeff U z k :=
    fun k hk z => laurentCoeff_boundary_periodic_tau hG hmixed hk z
  have hpoleOne : ∀ z : ℂ, meromorphicOrderAt U z < 0 → meromorphicOrderAt U (z + 1) < 0 :=
    fun z hz => pole_invariant_of_laurentCoeff_invariant hUmero hone hz
  have hpoleTau : ∀ z : ℂ, meromorphicOrderAt U z < 0 → meromorphicOrderAt U (z + τ) < 0 :=
    fun z hz => pole_invariant_of_laurentCoeff_invariant hUmero htau hz
  have hback : ∀ (t : ℂ), (∀ (k : ℤ), k < 0 → ∀ z : ℂ,
      laurentCoeff U (z + t) k = laurentCoeff U z k) →
      ∀ z : ℂ, meromorphicOrderAt U z < 0 → meromorphicOrderAt U (z - t) < 0 := by
    intro t hinv z hz
    obtain ⟨k, hk, hne⟩ :=
      (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero (hUmero z (Set.mem_univ z))).mp hz
    refine (meromorphicOrderAt_neg_iff_exists_laurentCoeff_ne_zero
      (hUmero (z - t) (Set.mem_univ _))).mpr ⟨k, hk, ?_⟩
    have hval := hinv k hk (z - t)
    rw [sub_add_cancel] at hval
    rw [← hval]
    exact hne
  have hpoleOneNeg := hback 1 hone
  have hpoleTauNeg := hback τ htau
  have hstep : ∀ (t : ℂ),
      (∀ z : ℂ, meromorphicOrderAt U z < 0 → meromorphicOrderAt U (z + t) < 0) →
      (∀ z : ℂ, meromorphicOrderAt U z < 0 → meromorphicOrderAt U (z - t) < 0) →
      ∀ (j : ℤ) (z : ℂ), meromorphicOrderAt U z < 0 →
        meromorphicOrderAt U (z - j • t) < 0 := by
    intro t hf hb j
    induction j using Int.induction_on with
    | zero => intro z hz; simpa using hz
    | succ n ih =>
        intro z hz
        have h1 := ih z hz
        have h2 := hb _ h1
        have harg : z - (n : ℤ) • t - t = z - ((n : ℤ) + 1) • t := by
          module
        rwa [harg] at h2
    | pred n ih =>
        intro z hz
        have h1 := ih z hz
        have h2 := hf _ h1
        have harg : z - (-(n : ℤ)) • t + t = z - (-(n : ℤ) - 1) • t := by
          module
        rwa [harg] at h2
  have hinv : ∀ (a b : ℤ) (z : ℂ), meromorphicOrderAt U z < 0 →
      meromorphicOrderAt U (z - (a • (1 : ℂ) + b • τ)) < 0 := by
    intro a b z hz
    have h1 := hstep 1 hpoleOne hpoleOneNeg a z hz
    have h2 := hstep τ hpoleTau hpoleTauNeg b _ h1
    have harg : z - a • (1 : ℂ) - b • τ = z - (a • (1 : ℂ) + b • τ) := by abel
    rwa [harg] at h2
  obtain ⟨P, hP⟩ := exists_finset_pole_classes hUmero
    (linearIndependent_one_of_im_pos hτ) hinv
  refine ⟨P, ?_⟩
  intro p hp
  have hterm : ∃ m : ℤ, laurentCoeff U (p + (m : ℂ) * σ) ℓ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hp
    rw [additiveOrbitalDivisorAt]
    have : ∀ m : ℤ, laurentCoeff U (p + (m : ℂ) * σ) ℓ = 0 := hcon
    rw [finsum_congr this, finsum_zero]
  obtain ⟨m, hm⟩ := hterm
  have hpole : meromorphicOrderAt U (p + (m : ℂ) * σ) < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero
      (hUmero _ (Set.mem_univ _)) hℓ hm
  obtain ⟨a, b, hmem⟩ := hP _ hpole
  refine ⟨p + (m : ℂ) * σ - (a • (1 : ℂ) + b • τ), hmem, ?_⟩
  refine ⟨a, b, -m, ?_⟩
  push_cast
  ring

/-! ## The descent -/

theorem periodicOneGerm_comp_add {G : ℂ → ℂ} (hper : PeriodicOneGerm G) (t : ℂ) :
    PeriodicOneGerm (fun w => G (w + t)) := by
  intro z
  have h := (tendsto_nhdsNE_add_const z t).eventually (hper (z + t))
  filter_upwards [h] with w hw
  show G (w + 1 + t) = G (w + t)
  rw [show w + 1 + t = w + t + 1 from by ring]
  exact hw

theorem mixedConstGerm_comp_add' {G : ℂ → ℂ} {τ σ Cst : ℂ}
    (hmixed : MixedConstGerm G τ σ Cst) (t : ℂ) :
    MixedConstGerm (fun w => G (w + t)) τ σ Cst := by
  intro z
  have h := (tendsto_nhdsNE_add_const z t).eventually (hmixed (z + t))
  filter_upwards [h] with w hw
  show G (w + τ + σ + t) - G (w + τ + t) - G (w + σ + t) + G (w + t) = Cst
  rw [show w + τ + σ + t = w + t + τ + σ from by ring,
    show w + τ + t = w + t + τ from by ring,
    show w + σ + t = w + t + σ from by ring]
  exact hw

set_option maxHeartbeats 1000000 in
/-- **The signature descends one depth.**  If the `t`-difference of a depth-two source has
vanishing orbital divisor, and `t` has infinite order modulo the period group, then the source
itself has vanishing orbital divisor. -/
theorem orbitalDivisor_eq_zero_of_shiftDiff_orbitalDivisor_eq_zero
    {G : ℂ → ℂ} {τ σ t : ℂ}
    (hG : MeromorphicOn G (Set.univ : Set ℂ)) (hper : PeriodicOneGerm G)
    {Cst : ℂ} (hmixed : MixedConstGerm G τ σ Cst)
    (hτ : 0 < τ.im)
    (hindep : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 → m = 0 ∧ n = 0 ∧ j = 0)
    (ht : ∀ n : ℤ, n • t ∈ tripticPeriodGroup τ σ → n = 0)
    {ℓ : ℤ} (hℓ : ℓ < 0)
    (hzero : ∀ p : ℂ, additiveOrbitalDivisorAt (HTGeometry.shiftDiffFun t G) σ p ℓ = 0)
    (p : ℂ) : additiveOrbitalDivisorAt G σ p ℓ = 0 := by
  classical
  have hGt : MeromorphicOn (fun w => G (w + t)) (Set.univ : Set ℂ) := fun z _ =>
    meromorphicAt_comp_add.mpr (hG (z + t) (Set.mem_univ _))
  have hinvR : ∀ q : ℂ,
      additiveOrbitalDivisorAt G σ (q + t) ℓ = additiveOrbitalDivisorAt G σ q ℓ := by
    intro q
    have hs1 : {m : ℤ | laurentCoeff (fun w : ℂ => G (w + σ + t) - G (w + t))
        (q + (m : ℂ) * σ) ℓ ≠ 0}.Finite := by
      have h := finite_support_orbitalDivisorTerm (F := fun w => G (w + t)) (τ := τ) (σ := σ)
        hGt (periodicOneGerm_comp_add hper t) (mixedConstGerm_comp_add' hmixed t) hτ hindep q hℓ
      refine h.subset ?_
      intro m hm
      simpa [show ∀ w : ℂ, w + t + σ = w + σ + t from fun w => by ring] using hm
    have hs2 : {m : ℤ | laurentCoeff (fun w : ℂ => G (w + σ) - G w)
        (q + (m : ℂ) * σ) ℓ ≠ 0}.Finite :=
      finite_support_orbitalDivisorTerm hG hper hmixed hτ hindep q hℓ
    have hd := additiveOrbitalDivisorAt_shiftDiffFun (G := G) (σ := σ) (c := t) (p := q) (ℓ := ℓ)
      hG hs1 hs2
    rw [hzero q] at hd
    linear_combination -hd
  obtain ⟨S, hS⟩ := exists_finset_orbitalDivisor_classes hG hper hmixed hτ hℓ
  exact HTGeometry.eq_zero_of_invariant_of_finite_classes (R := fun q =>
    additiveOrbitalDivisorAt G σ q ℓ) (S := S) (H := tripticPeriodGroup τ σ)
    (fun q hq => hS q hq) ht hinvR p

end

end GaloisForLFunctions
