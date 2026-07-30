import GaloisForLFunctions.HTGeometry.PrescribedResidueBalancedAtom
import GaloisForLFunctions.HTGeometry.PolynomialProuhetLock

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- Shift a bounded nonnegative offset by the left endpoint `q-K` of a
coefficient window. -/
def windowShift (q K r : ℕ) : ℕ := q - K + r

theorem windowShift_injective {q K : ℕ} :
    Function.Injective (windowShift q K) := by
  intro a b h
  simp only [windowShift] at h
  omega

/-- Multiplicity key of a bounded pattern after translation to the window
center `q`. -/
def shiftedAtomPatternKey {M D : ℕ} (q K : ℕ)
    (p : Fin M → Fin (D + 1)) : ℕ →₀ ℕ :=
  Finsupp.mapDomain (windowShift q K) (atomPatternKey p)

theorem shiftedAtomPatternKey_eq_sum {M D : ℕ} (q K : ℕ)
    (p : Fin M → Fin (D + 1)) :
    shiftedAtomPatternKey q K p =
      ∑ j : Fin M, Finsupp.single (windowShift q K (j : ℕ)) (p j : ℕ) := by
  classical
  rw [shiftedAtomPatternKey, atomPatternKey, Finsupp.mapDomain_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  exact Finsupp.mapDomain_single

theorem shiftedAtomPatternKey_count {M D : ℕ} {q K : ℕ}
    (p : Fin M → Fin (D + 1)) :
    (shiftedAtomPatternKey q K p).sum (fun _ k => k) = ∑ j, (p j : ℕ) := by
  classical
  rw [shiftedAtomPatternKey_eq_sum,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun j : Fin M =>
        Finsupp.single (windowShift q K (j : ℕ)) (p j : ℕ))
      (h := fun _ k => k)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.sum_single_index]
    simp
  · intro a
    simp
  · intro a b c
    simp

theorem atomPatternKey_weightedSum {M D : ℕ}
    (p : Fin M → Fin (D + 1)) :
    (atomPatternKey p).sum (fun i k => i * k) =
      ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
  classical
  rw [atomPatternKey,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun j : Fin M => Finsupp.single (j : ℕ) (p j : ℕ))
      (h := fun i k => i * k)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.sum_single_index]
    simp
  · intro a
    simp
  · intro a b c
    simp [Nat.mul_add]

theorem shiftedAtomPatternKey_weightedSum {M D q K : ℕ}
    (p : Fin M → Fin (D + 1)) :
    (shiftedAtomPatternKey q K p).sum (fun i k => i * k) =
      ∑ j : Fin M, windowShift q K (j : ℕ) * (p j : ℕ) := by
  classical
  rw [shiftedAtomPatternKey_eq_sum,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun j : Fin M =>
        Finsupp.single (windowShift q K (j : ℕ)) (p j : ℕ))
      (h := fun i k => i * k)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finsupp.sum_single_index]
    simp
  · intro a
    simp
  · intro a b c
    simp [Nat.mul_add]

theorem shiftedAtomPatternKey_weightedSum_eq {M D q K : ℕ}
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ j, (p j : ℕ)) = D) :
    (shiftedAtomPatternKey q K p).sum (fun i k => i * k) =
      D * (q - K) + ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
  rw [shiftedAtomPatternKey_weightedSum]
  calc
    ∑ j : Fin M, windowShift q K (j : ℕ) * (p j : ℕ) =
        (q - K) * (∑ j, (p j : ℕ)) +
          ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
      simp only [windowShift, Nat.add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    _ = D * (q - K) + ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
      rw [hcount, Nat.mul_comm]

theorem key_comp_equiv {D E : ℕ} (e : Fin D ≃ Fin E) (s : Fin E → ℕ) :
    key (fun i => s (e i)) = key s := by
  classical
  rw [key, key]
  exact Equiv.sum_comp e (fun i => Finsupp.single (s i) 1)

/-- Fixed assignments of the `D` labelled jet factors to the multiplicities
of a bounded window pattern. -/
def atomPatternAssignments {M D : ℕ} (p : Fin M → Fin (D + 1)) :
    Finset (Fin D → Fin M) :=
  Finset.univ.filter fun g => key (fun t => (g t : ℕ)) = atomPatternKey p

theorem mem_atomPatternAssignments {M D : ℕ} {p : Fin M → Fin (D + 1)}
    {g : Fin D → Fin M} :
    g ∈ atomPatternAssignments p ↔
      key (fun t => (g t : ℕ)) = atomPatternKey p := by
  simp [atomPatternAssignments]

theorem atomPatternAssignment_sum {M D : ℕ}
    (p : Fin M → Fin (D + 1)) (g : Fin D → Fin M)
    (hg : g ∈ atomPatternAssignments p) :
    ∑ t, (g t : ℕ) = ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
  rw [← key_weighted_sum (fun t => (g t : ℕ)), mem_atomPatternAssignments.mp hg,
    atomPatternKey_weightedSum]

theorem key_windowShift_eq_shiftedAtomPatternKey {M D q K : ℕ}
    (p : Fin M → Fin (D + 1)) (g : Fin D → Fin M)
    (hg : g ∈ atomPatternAssignments p) :
    key (fun t => windowShift q K (g t : ℕ)) = shiftedAtomPatternKey q K p := by
  classical
  have hkey := (mem_atomPatternAssignments.mp hg)
  have hmap := congrArg (Finsupp.mapDomain (windowShift q K)) hkey
  rw [key, Finsupp.mapDomain_finsetSum] at hmap
  have hleft :
      (∑ x : Fin D,
          Finsupp.mapDomain (windowShift q K)
            (Finsupp.single ((g x : Fin M) : ℕ) 1)) =
        key (fun t => windowShift q K (g t : ℕ)) := by
    rw [key]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finsupp.mapDomain_single]
  rw [hleft] at hmap
  simpa [shiftedAtomPatternKey] using hmap

/-- A source tuple has a translated bounded-pattern key iff it comes from a
unique labelled assignment of its coordinates to that pattern. -/
theorem existsUnique_atomPatternAssignment_of_key_eq_shifted
    {M D q K : ℕ} (p : Fin M → Fin (D + 1)) (s : Fin D → ℕ)
    (hkey : key s = shiftedAtomPatternKey q K p) :
    ∃! g : Fin D → Fin M,
      g ∈ atomPatternAssignments p ∧
        ∀ t, s t = windowShift q K (g t : ℕ) := by
  classical
  have hsource : ∀ t, ∃ j : Fin M, s t = windowShift q K (j : ℕ) := by
    intro t
    have hpos : key s (s t) ≠ 0 := by
      rw [key_count_map]
      exact Multiset.count_ne_zero.mpr (by simp)
    have hmem : s t ∈ (shiftedAtomPatternKey q K p).support := by
      rw [← hkey]
      exact Finsupp.mem_support_iff.mpr hpos
    rw [shiftedAtomPatternKey,
      Finsupp.mapDomain_support_of_injective windowShift_injective] at hmem
    obtain ⟨j, hj, hjs⟩ := Finset.mem_image.mp hmem
    have hjlt : j < M := by
      by_contra hjnot
      have hz : atomPatternKey p j = 0 := by
        rw [atomPatternKey_apply]
        simp [Nat.not_lt.mp hjnot]
      exact Finsupp.mem_support_iff.mp hj hz
    exact ⟨⟨j, hjlt⟩, by simpa using hjs.symm⟩
  choose g hgsource using hsource
  have hgkey : key (fun t => (g t : ℕ)) = atomPatternKey p := by
    apply Finsupp.mapDomain_injective windowShift_injective
    calc
      Finsupp.mapDomain (windowShift q K) (key (fun t => (g t : ℕ))) =
          key s := by
        rw [key, Finsupp.mapDomain_finsetSum, key]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finsupp.mapDomain_single, hgsource]
      _ = shiftedAtomPatternKey q K p := hkey
      _ = Finsupp.mapDomain (windowShift q K) (atomPatternKey p) := rfl
  refine ⟨g, ⟨mem_atomPatternAssignments.mpr hgkey, hgsource⟩, ?_⟩
  intro g' hg'
  funext t
  apply Fin.ext
  exact windowShift_injective ((hg'.2 t).symm.trans (hgsource t))

theorem eval_descPochhammer_comp_windowShift (q K r μ : ℕ) (hK : K ≤ q) :
    (((descPochhammer ℂ μ).comp
      (Polynomial.X + Polynomial.C (((r : ℤ) - (K : ℤ) : ℤ) : ℂ))).eval (q : ℂ)) =
        ((windowShift q K r).descFactorial μ : ℂ) := by
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have harg : (q : ℂ) + (((r : ℤ) - (K : ℤ) : ℤ) : ℂ) =
      (windowShift q K r : ℕ) := by
    calc
      (q : ℂ) + (((r : ℤ) - (K : ℤ) : ℤ) : ℂ) =
          (((q : ℤ) + (r : ℤ) - (K : ℤ) : ℤ) : ℂ) := by
            push_cast
            ring
      _ = ((q - K + r : ℕ) : ℂ) := by
        congr 1
        exact_mod_cast (by omega : (q : ℤ) + r - K = (q - K + r : ℕ))
      _ = (windowShift q K r : ℕ) := by rfl
  rw [harg]
  exact descPochhammer_eval_eq_descFactorial ℂ _ _

/-- Top-degree monomials whose conserved source sum matches the bounded
pattern at coefficient levels `D*q+τ`. -/
def polynomialPatternJetGroup (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {M : ℕ}
    (p : Fin M → Fin (D + 1)) : Finset (Fin (n + 2) →₀ ℕ) :=
  Q.support.filter fun m =>
    jetMonomialDegree n m = D ∧
      (∑ j : Fin M, (j : ℕ) * (p j : ℕ)) + m 0 =
        D * K + τ + jetMonomialOrder n m

theorem polynomialPatternJetGroup_degree {n D K τ M : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) :
    jetMonomialDegree n m.1 = D :=
  ((Finset.mem_filter.mp m.2).2).1

noncomputable def polynomialPatternJetCast {n D K τ M : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) :
    Fin (jetMonomialDegree n m.1) ≃ Fin D :=
  Equiv.cast (congrArg Fin (polynomialPatternJetGroup_degree m))

/-- Falling-factorial polynomial contributed by one fixed assignment of the
labelled jet factors to a bounded source pattern. -/
noncomputable def polynomialPatternAssignmentPoly {n D K τ M : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M) :
    Polynomial ℂ :=
  ∏ t : Fin (jetMonomialDegree n m.1),
    (descPochhammer ℂ (flatOrder (fun j => m.1 j.succ) t)).comp
      (Polynomial.X + Polynomial.C
        (((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) - (K : ℤ) : ℤ) : ℂ))

theorem eval_polynomialPatternAssignmentPoly {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M)
    (hK : K ≤ q) :
    (polynomialPatternAssignmentPoly m g).eval (q : ℂ) =
      ∏ t : Fin (jetMonomialDegree n m.1),
        ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
          (flatOrder (fun j => m.1 j.succ) t) : ℂ) := by
  rw [polynomialPatternAssignmentPoly, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro t _
  exact eval_descPochhammer_comp_windowShift q K _ _ hK

/-- The grouped bounded-pattern weight polynomial.  Repeated source indices
are represented by the finite set of distinct labelled assignments, so no
division or injectivity assumption on the pattern is needed. -/
noncomputable def polynomialPatternWeightPoly (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {M : ℕ}
    (p : Fin M → Fin (D + 1)) : Polynomial ℂ :=
  ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
    Polynomial.C (MvPolynomial.coeff m.1 Q) *
      ∑ g ∈ atomPatternAssignments p, polynomialPatternAssignmentPoly m g

theorem eval_polynomialPatternWeightPoly (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {M q : ℕ}
    (p : Fin M → Fin (D + 1)) (hK : K ≤ q) :
    (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) =
      ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
        MvPolynomial.coeff m.1 Q *
          ∑ g ∈ atomPatternAssignments p,
            ∏ t : Fin (jetMonomialDegree n m.1),
              ((windowShift q K (g (polynomialPatternJetCast m t) : ℕ)).descFactorial
                (flatOrder (fun j => m.1 j.succ) t) : ℂ) := by
  rw [polynomialPatternWeightPoly, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact eval_polynomialPatternAssignmentPoly m g hK

/-- Finite labelled realizations of a bounded pattern by the eligible
top-degree jet monomials. -/
def polynomialPatternPairs (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {M : ℕ}
    (p : Fin M → Fin (D + 1)) :
    Finset (Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M) :=
  (polynomialPatternJetGroup n D K τ Q p).attach.sigma
    (fun _ => atomPatternAssignments p)

/-- Antidiagonal split attached to one fixed pattern assignment. -/
noncomputable def polynomialPatternSplit {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (y : Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M) :
    Fin (jetMonomialDegree n y.1.1) →₀ ℕ :=
  Finsupp.onFinset Finset.univ
    (fun t => windowShift q K (y.2 (polynomialPatternJetCast y.1 t) : ℕ) -
      flatOrder (fun j => y.1.1 j.succ) t)
    (fun _ _ => Finset.mem_univ _)

/-- The original ADE sigma atom represented by a fixed bounded pattern
assignment. -/
  noncomputable def polynomialPatternSigma {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (y : Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M) :
    Σ m : Fin (n + 2) →₀ ℕ, Fin (jetMonomialDegree n m) →₀ ℕ :=
  ⟨y.1.1, polynomialPatternSplit (q := q) y⟩

theorem flatOrder_le_windowShift_of_large {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M)
    (hlarge : K + n ≤ q) (t : Fin (jetMonomialDegree n m.1)) :
    flatOrder (fun j => m.1 j.succ) t ≤
      windowShift q K (g (polynomialPatternJetCast m t) : ℕ) := by
  have hflat := flatOrder_le_jetBound (fun j => m.1 j.succ) t
  have hn : n ≤ q - K := by omega
  exact hflat.trans (hn.trans (Nat.le_add_right _ _))

theorem polynomialPatternSplit_add_order {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (y : Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M)
    (hlarge : K + n ≤ q)
    (t : Fin (jetMonomialDegree n y.1.1)) :
    polynomialPatternSplit (q := q) y t +
        flatOrder (fun j => y.1.1 j.succ) t =
      windowShift q K (y.2 (polynomialPatternJetCast y.1 t) : ℕ) := by
  rw [polynomialPatternSplit, Finsupp.onFinset_apply]
  exact Nat.sub_add_cancel (flatOrder_le_windowShift_of_large y.1 y.2 hlarge t)

theorem polynomialPatternSigma_mem_fiber {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (hlarge : K + n ≤ q)
    (y : Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M)
    (hy : y ∈ polynomialPatternPairs n D K τ Q p) :
    polynomialPatternSigma (q := q) y ∈
      (sigmaIdx n (D * q + τ) Q).filter
        (fun x => atomKeyOf n x = shiftedAtomPatternKey q K p) := by
  classical
  have hmAttach : y.1 ∈ (polynomialPatternJetGroup n D K τ Q p).attach :=
    (Finset.mem_sigma.mp hy).1
  have hg : y.2 ∈ atomPatternAssignments p := (Finset.mem_sigma.mp hy).2
  have hmGroup := y.1.2
  have hmQ : y.1.1 ∈ Q.support := (Finset.mem_filter.mp hmGroup).1
  have hdegree : jetMonomialDegree n y.1.1 = D :=
    polynomialPatternJetGroup_degree y.1
  have helig := ((Finset.mem_filter.mp hmGroup).2).2
  let e := polynomialPatternJetCast y.1
  let μ : Fin (jetMonomialDegree n y.1.1) → ℕ :=
    flatOrder (fun j => y.1.1 j.succ)
  let src : Fin (jetMonomialDegree n y.1.1) → ℕ := fun t =>
    windowShift q K (y.2 (e t) : ℕ)
  have hμsum : ∑ t, μ t = jetMonomialOrder n y.1.1 := by
    exact flatOrder_sum (fun j => y.1.1 j.succ)
  have hgSum := atomPatternAssignment_sum p y.2 hg
  have hsrcsum : (∑ t, src t) =
      D * (q - K) + ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
    calc
      ∑ t, src t = ∑ i : Fin D, windowShift q K (y.2 i : ℕ) := by
        exact Equiv.sum_comp e (fun i => windowShift q K (y.2 i : ℕ))
      _ = D * (q - K) + ∑ i : Fin D, (y.2 i : ℕ) := by
        simp [windowShift, Finset.sum_add_distrib]
      _ = D * (q - K) + ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by rw [hgSum]
  have hsplitSum : (∑ t, polynomialPatternSplit (q := q) y t) + ∑ t, μ t =
      ∑ t, src t := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    exact polynomialPatternSplit_add_order y hlarge t
  have hmul : D * (q - K) + D * K = D * q := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel]
    exact Nat.mul_le_mul_left D (by omega)
  have hmN : y.1.1 0 ≤ D * q + τ := by
    rw [hμsum, hsrcsum] at hsplitSum
    omega
  have hsplitLevel : (∑ t, polynomialPatternSplit (q := q) y t) =
      D * q + τ - y.1.1 0 := by
    rw [hμsum, hsrcsum] at hsplitSum
    omega
  have hkeySrc : key src = shiftedAtomPatternKey q K p := by
    calc
      key src = key (fun i : Fin D => windowShift q K (y.2 i : ℕ)) :=
        key_comp_equiv e (fun i : Fin D => windowShift q K (y.2 i : ℕ))
      _ = shiftedAtomPatternKey q K p :=
        key_windowShift_eq_shiftedAtomPatternKey p y.2 hg
  apply Finset.mem_filter.mpr
  constructor
  · change (Sigma.mk y.1.1 (polynomialPatternSplit (q := q) y)) ∈
      sigmaIdx n (D * q + τ) Q
    rw [sigmaIdx, Finset.mem_sigma]
    refine ⟨Finset.mem_filter.mpr ⟨hmQ, hmN⟩, ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, ?_⟩
    simpa using! hsplitLevel
    intro a ha
    exact Finset.mem_univ a
  · change key (fun t => polynomialPatternSplit (q := q) y t + μ t) = _
    rw [show (fun t => polynomialPatternSplit (q := q) y t + μ t) = src from
      funext (fun t => polynomialPatternSplit_add_order y hlarge t)]
    exact hkeySrc

theorem polynomialPatternSigma_injective {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (hlarge : K + n ≤ q) :
    Function.Injective
      (polynomialPatternSigma (q := q) :
        (Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M) →
          Σ m : Fin (n + 2) →₀ ℕ, Fin (jetMonomialDegree n m) →₀ ℕ) := by
  classical
  rintro ⟨m, g⟩ ⟨m', g'⟩ h
  have hmm : m = m' := by
    apply Subtype.ext
    exact (Sigma.ext_iff.mp h).1
  subst m'
  have hsplit : polynomialPatternSplit (q := q) (Sigma.mk m g) =
      polynomialPatternSplit (q := q) (Sigma.mk m g') :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  have hgg : g = g' := by
    funext i
    let t := (polynomialPatternJetCast m).symm i
    have ht := Finsupp.ext_iff.mp hsplit t
    have hsrc : windowShift q K (g i : ℕ) = windowShift q K (g' i : ℕ) := by
      have hleft := polynomialPatternSplit_add_order (q := q)
        (Sigma.mk m g) hlarge t
      have hright := polynomialPatternSplit_add_order (q := q)
        (Sigma.mk m g') hlarge t
      simp only [Equiv.apply_symm_apply, t] at hleft hright
      exact hleft.symm.trans ((congrArg (fun z => z +
        flatOrder (fun j => m.1 j.succ) t) ht).trans hright)
    apply Fin.ext
    exact windowShift_injective hsrc
  subst g'
  rfl

theorem exists_polynomialPatternPair_of_mem_fiber {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (hcount : (∑ j, (p j : ℕ)) = D) (hlarge : K + n ≤ q)
    (x : Σ m : Fin (n + 2) →₀ ℕ, Fin (jetMonomialDegree n m) →₀ ℕ)
    (hx : x ∈ (sigmaIdx n (D * q + τ) Q).filter
      (fun x => atomKeyOf n x = shiftedAtomPatternKey q K p)) :
    ∃ y ∈ polynomialPatternPairs n D K τ Q p,
      polynomialPatternSigma (q := q) y = x := by
  classical
  obtain ⟨hxSigma, hxKey⟩ := Finset.mem_filter.mp hx
  rw [sigmaIdx] at hxSigma
  change (Sigma.mk x.1 x.2) ∈
    (Q.support.filter (fun m => m 0 ≤ D * q + τ)).sigma
      (fun m => (Finset.univ : Finset (Fin (jetMonomialDegree n m))).finsuppAntidiag
        (D * q + τ - m 0)) at hxSigma
  rw [Finset.mem_sigma] at hxSigma
  obtain ⟨hmBase, hlAnti⟩ := hxSigma
  obtain ⟨hmQ, hmN⟩ := Finset.mem_filter.mp hmBase
  have hlSum := (Finset.mem_finsuppAntidiag.mp hlAnti).1
  have hdegree : jetMonomialDegree n x.1 = D := by
    rw [jetMonomialDegree, ← atomKeyOf_count n x, hxKey,
      shiftedAtomPatternKey_count, hcount]
  let μ : Fin (jetMonomialDegree n x.1) → ℕ :=
    flatOrder (fun j => x.1 j.succ)
  let src : Fin (jetMonomialDegree n x.1) → ℕ := fun t => x.2 t + μ t
  have hμsum : ∑ t, μ t = jetMonomialOrder n x.1 := by
    exact flatOrder_sum (fun j => x.1 j.succ)
  have hsrcKey : key src = shiftedAtomPatternKey q K p := by
    simpa [src, μ, atomKeyOf] using! hxKey
  have hsrcSumLevel : (∑ t, src t) =
      D * q + τ - x.1 0 + jetMonomialOrder n x.1 := by
    dsimp [src]
    rw [Finset.sum_add_distrib, hμsum, hlSum]
  have hsrcSumPattern : (∑ t, src t) =
      D * (q - K) + ∑ j : Fin M, (j : ℕ) * (p j : ℕ) := by
    rw [← key_weighted_sum src, hsrcKey,
      shiftedAtomPatternKey_weightedSum_eq p hcount]
  have hmul : D * (q - K) + D * K = D * q := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel]
    exact Nat.mul_le_mul_left D (by omega)
  have helig : (∑ j : Fin M, (j : ℕ) * (p j : ℕ)) + x.1 0 =
      D * K + τ + jetMonomialOrder n x.1 := by
    have hNsub : D * q + τ - x.1 0 + x.1 0 = D * q + τ :=
      Nat.sub_add_cancel hmN
    omega
  have hmGroup : x.1 ∈ polynomialPatternJetGroup n D K τ Q p := by
    rw [polynomialPatternJetGroup, Finset.mem_filter]
    exact ⟨hmQ, hdegree, helig⟩
  let m : ↥(polynomialPatternJetGroup n D K τ Q p) := ⟨x.1, hmGroup⟩
  let e := polynomialPatternJetCast m
  let s : Fin D → ℕ := fun i => src (e.symm i)
  have hsKey : key s = shiftedAtomPatternKey q K p := by
    calc
      key s = key src := key_comp_equiv e.symm src
      _ = shiftedAtomPatternKey q K p := hsrcKey
  obtain ⟨g, hg, hgUnique⟩ :=
    existsUnique_atomPatternAssignment_of_key_eq_shifted p s hsKey
  let y : Σ m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M :=
    Sigma.mk m g
  have hy : y ∈ polynomialPatternPairs n D K τ Q p := by
    rw [polynomialPatternPairs, Finset.mem_sigma]
    exact ⟨Finset.mem_attach _ _, hg.1⟩
  refine ⟨y, hy, ?_⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    ext t
    change polynomialPatternSplit (q := q) (Sigma.mk m g) t = x.2 t
    rw [polynomialPatternSplit, Finsupp.onFinset_apply]
    have hst := hg.2 (e t)
    change src (e.symm (e t)) = windowShift q K (g (e t) : ℕ) at hst
    rw [e.symm_apply_apply] at hst
    rw [← hst]
    simp [src, μ, m]

theorem atomDescProd_polynomialPatternSigma {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (hlarge : K + n ≤ q)
    (y : Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M) :
    atomDescProd n (polynomialPatternSigma (q := q) y) =
      ∏ t : Fin (jetMonomialDegree n y.1.1),
        ((windowShift q K (y.2 (polynomialPatternJetCast y.1 t) : ℕ)).descFactorial
          (flatOrder (fun j => y.1.1 j.succ) t) : ℂ) := by
  rw [atomDescProd]
  apply Finset.prod_congr rfl
  intro t _
  change (((polynomialPatternSplit (q := q) y t +
      flatOrder (fun j => y.1.1 j.succ) t).descFactorial
        (flatOrder (fun j => y.1.1 j.succ) t) : ℕ) : ℂ) = _
  rw [polynomialPatternSplit_add_order y hlarge t]

theorem sum_polynomialPatternPairs_eq_fiber {n D K τ M q : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (hcount : (∑ j, (p j : ℕ)) = D) (hlarge : K + n ≤ q) :
    (∑ y ∈ polynomialPatternPairs n D K τ Q p,
        MvPolynomial.coeff y.1.1 Q *
          atomDescProd n (polynomialPatternSigma (q := q) y)) =
      ∑ x ∈ (sigmaIdx n (D * q + τ) Q).filter
          (fun x => atomKeyOf n x = shiftedAtomPatternKey q K p),
        MvPolynomial.coeff x.1 Q * atomDescProd n x := by
  classical
  let fiber := (sigmaIdx n (D * q + τ) Q).filter
    (fun x => atomKeyOf n x = shiftedAtomPatternKey q K p)
  have hback : ∀ x ∈ fiber,
      ∃ y ∈ polynomialPatternPairs n D K τ Q p,
        polynomialPatternSigma (q := q) y = x := by
    intro x hx
    exact exists_polynomialPatternPair_of_mem_fiber hcount hlarge x hx
  let back : ∀ x, x ∈ fiber →
      (Σ _m : ↥(polynomialPatternJetGroup n D K τ Q p), Fin D → Fin M) :=
    fun x hx => (hback x hx).choose
  have hbackMem : ∀ x (hx : x ∈ fiber),
      back x hx ∈ polynomialPatternPairs n D K τ Q p :=
    fun x hx => (hback x hx).choose_spec.1
  have hbackEq : ∀ x (hx : x ∈ fiber),
      polynomialPatternSigma (q := q) (back x hx) = x :=
    fun x hx => (hback x hx).choose_spec.2
  change (∑ y ∈ polynomialPatternPairs n D K τ Q p,
      MvPolynomial.coeff y.1.1 Q * atomDescProd n (polynomialPatternSigma (q := q) y)) =
    ∑ x ∈ fiber, MvPolynomial.coeff x.1 Q * atomDescProd n x
  refine Finset.sum_bij'
    (fun y _ => polynomialPatternSigma (q := q) y)
    (fun x hx => back x hx) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact polynomialPatternSigma_mem_fiber hlarge y hy
  · intro x hx
    exact hbackMem x hx
  · intro y hy
    apply polynomialPatternSigma_injective hlarge
    exact hbackEq (polynomialPatternSigma (q := q) y)
      (polynomialPatternSigma_mem_fiber hlarge y hy)
  · intro x hx
    exact hbackEq x hx
  · intro y hy
    rfl

/-- Stable bounded-pattern polynomiality of the grouped ADE weight, including
patterns with repeated source indices. -/
theorem aevalWeight_shiftedAtomPatternKey_eq_eval_poly (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) {M q : ℕ}
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ j, (p j : ℕ)) = D) (hlarge : K + n ≤ q) :
    aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
      (polynomialPatternWeightPoly n D K τ Q p).eval (q : ℂ) := by
  rw [aevalWeight, eval_polynomialPatternWeightPoly n D K τ Q p (by omega)]
  have hpairs := sum_polynomialPatternPairs_eq_fiber
    (Q := Q) (p := p) (τ := τ) hcount hlarge
  rw [← hpairs]
  rw [polynomialPatternPairs, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [atomDescProd_polynomialPatternSigma hlarge (Sigma.mk m g)]

/-- Integer version of one assignment polynomial. -/
noncomputable def polynomialPatternAssignmentPolyInt {n D K τ M : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M) :
    Polynomial ℤ :=
  ∏ t : Fin (jetMonomialDegree n m.1),
    (descPochhammer ℤ (flatOrder (fun j => m.1 j.succ) t)).comp
      (Polynomial.X + Polynomial.C
        ((((g (polynomialPatternJetCast m t) : Fin M) : ℕ) : ℤ) - (K : ℤ)))

theorem map_polynomialPatternAssignmentPolyInt {n D K τ M : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {p : Fin M → Fin (D + 1)}
    (m : ↥(polynomialPatternJetGroup n D K τ Q p)) (g : Fin D → Fin M) :
    (polynomialPatternAssignmentPolyInt m g).map (Int.castRingHom ℂ) =
      polynomialPatternAssignmentPoly m g := by
  rw [polynomialPatternAssignmentPolyInt, polynomialPatternAssignmentPoly,
    Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro t _
  rw [Polynomial.map_comp, descPochhammer_map]
  congr 1
  simp

/-- Integer polynomial obtained from fixed integer coefficients of the ADE
monomials. -/
noncomputable def polynomialPatternWeightPolyInt (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (c : (Fin (n + 2) →₀ ℕ) → ℤ) {M : ℕ}
    (p : Fin M → Fin (D + 1)) : Polynomial ℤ :=
  ∑ m ∈ (polynomialPatternJetGroup n D K τ Q p).attach,
    Polynomial.C (c m.1) *
      ∑ g ∈ atomPatternAssignments p, polynomialPatternAssignmentPolyInt m g

theorem map_polynomialPatternWeightPolyInt (n D K τ : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (c : (Fin (n + 2) →₀ ℕ) → ℤ)
    (hc : ∀ m, MvPolynomial.coeff m Q = (c m : ℂ)) {M : ℕ}
    (p : Fin M → Fin (D + 1)) :
    (polynomialPatternWeightPolyInt n D K τ Q c p).map (Int.castRingHom ℂ) =
      polynomialPatternWeightPoly n D K τ Q p := by
  rw [polynomialPatternWeightPolyInt, polynomialPatternWeightPoly, Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.map_mul, Polynomial.map_C, hc, Polynomial.map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro g hg
  exact map_polynomialPatternAssignmentPolyInt m g

/-- Integer-polynomial realization of every repeated bounded-pattern weight. -/
theorem exists_intPolynomial_aevalWeight_shiftedAtomPatternKey
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQ : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    {M : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ j, (p j : ℕ)) = D) :
    ∃ W : Polynomial ℤ, ∀ q, K + n ≤ q →
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
        ((W.eval (q : ℤ) : ℤ) : ℂ) := by
  classical
  choose c hc using hQ
  let W := polynomialPatternWeightPolyInt n D K τ Q c p
  refine ⟨W, fun q hlarge => ?_⟩
  rw [aevalWeight_shiftedAtomPatternKey_eq_eval_poly n D K τ Q p hcount hlarge]
  have hmap := map_polynomialPatternWeightPolyInt n D K τ Q c hc p
  rw [← hmap]
  simpa [W] using
    (Polynomial.eval_map_apply (p := polynomialPatternWeightPolyInt n D K τ Q c p)
      (f := Int.castRingHom ℂ) (x := (q : ℤ)))

theorem exists_nonzero_intPolynomial_aevalWeight_shiftedAtomPatternKey
    (n D K τ : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQ : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    {M q₀ : ℕ} (p : Fin M → Fin (D + 1))
    (hcount : (∑ j, (p j : ℕ)) = D) (hlarge₀ : K + n ≤ q₀)
    (hw₀ : aevalWeight n (D * q₀ + τ) Q (shiftedAtomPatternKey q₀ K p) ≠ 0) :
    ∃ W : Polynomial ℤ, W ≠ 0 ∧ ∀ q, K + n ≤ q →
      aevalWeight n (D * q + τ) Q (shiftedAtomPatternKey q K p) =
        ((W.eval (q : ℤ) : ℤ) : ℂ) := by
  obtain ⟨W, hW⟩ :=
    exists_intPolynomial_aevalWeight_shiftedAtomPatternKey n D K τ Q hQ p hcount
  have hWne : W ≠ 0 := by
    intro hzero
    apply hw₀
    rw [hW q₀ hlarge₀, hzero, Polynomial.eval_zero]
    simp
  exact ⟨W, hWne, hW⟩

theorem intPolynomial_eventually_eval_ne_zero (W : Polynomial ℤ) (hW : W ≠ 0) :
    ∃ Q₀ : ℕ, ∀ q ≥ Q₀, W.eval (q : ℤ) ≠ 0 := by
  let WC := W.map (Int.castRingHom ℂ)
  have hWC : WC ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hW
  obtain ⟨Q₀, hQ₀⟩ := poly_eventually_ne_zero_nat WC hWC
  refine ⟨Q₀, fun q hq hzero => ?_⟩
  apply hQ₀ q hq
  change (W.map (Int.castRingHom ℂ)).eval (q : ℂ) = 0
  calc
    (W.map (Int.castRingHom ℂ)).eval (q : ℂ) =
        ((W.eval (q : ℤ) : ℤ) : ℂ) := by
      simpa using (Polynomial.eval_map_apply (p := W)
        (f := Int.castRingHom ℂ) (x := (q : ℤ)))
    _ = 0 := by rw [hzero]; simp

end

end GaloisForLFunctions
