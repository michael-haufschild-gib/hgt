import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.PauliCharacterFirstDefectCovariance

/-!
# Noncontextuality of onsite Pauli supports

Two independent noncommuting onsite pairs obstruct the noncontextual
decomposition of Projansky, Wang, Reiss and Whitfield (arXiv:2611.26315,
Definition 3). Without bond terms this obstruction is exact: at most one
site may support more than one Pauli axis. In the Gaussian chain the
obstruction holds on every prefix with at least two sites, on the same draw.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Noncentral terms are those with a noncommuting partner in the given support. -/
def PauliNoncentral {ι R : Type*} [Mul R] (A : ι → R) (i : ι) : Prop :=
  ∃ j, ¬ Commute (A i) (A j)

/-- On the noncentral part of a Pauli family, commutation must be transitive. -/
def PauliNoncontextual {ι R : Type*} [Mul R] (A : ι → R) : Prop :=
  ∀ i j k, PauliNoncentral A i → PauliNoncentral A j → PauliNoncentral A k →
    Commute (A i) (A j) → Commute (A i) (A k) → Commute (A j) (A k)

/-- Two noncommuting pairs, with commuting cross terms from one endpoint,
certify contextuality in any family containing them. -/
theorem not_pauliNoncontextual_of_pairs {ι R : Type*} [Mul R] (A : ι → R)
    (i i' j j' : ι) :
    (¬ Commute (A i) (A i')) ∧ (¬ Commute (A j) (A j')) ∧
      Commute (A i) (A j) ∧ Commute (A i) (A j') →
      ¬ PauliNoncontextual A := by
  rintro ⟨hi, hj, hij, hij'⟩ h
  exact hj (h i j j' ⟨i', hi⟩ ⟨j', hj⟩ ⟨j, fun H => hj H.symm⟩ hij hij')

/-- The conjugation character detects commutation because Pauli words are involutions. -/
theorem finitePauli_commute_iff_sign {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P Q : σ → Option (Fin 3)) :
    Commute (finitePauliMatrix P) (finitePauliMatrix Q) ↔
      finitePauliConjugationSign P Q = 1 := by
  have hQ : finitePauliMatrix Q ≠ 0 := by
    intro h
    have hc := finitePauliMatrix_mul_self Q
    rw [h, Matrix.zero_mul] at hc
    exact zero_ne_one hc
  have hP (X : Matrix (σ → Bool) (σ → Bool) ℂ) :
      X * finitePauliMatrix P * finitePauliMatrix P = X := by
    rw [Matrix.mul_assoc, finitePauliMatrix_mul_self, Matrix.mul_one]
  constructor
  · intro h
    have hh := finitePauliMatrix_conj P Q
    rw [h.eq, hP] at hh
    have hz : (finitePauliConjugationSign P Q - 1) • finitePauliMatrix Q = 0 := by
      rw [sub_smul, one_smul, ← hh, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hQ)
  · intro h
    have hh := finitePauliMatrix_conj P Q
    rw [h, one_smul] at hh
    change finitePauliMatrix P * finitePauliMatrix Q = finitePauliMatrix Q * finitePauliMatrix P
    simpa only [hP] using congrArg (fun X => X * finitePauliMatrix P) hh

variable {n : ℕ}

/-- Onsite words fail to commute precisely for different axes on the same site. -/
theorem commute_onsitePauli_iff (i j : Fin (n + 2)) (a b : Fin 3) :
    Commute (finitePauliMatrix (onsiteWord i a)) (finitePauliMatrix (onsiteWord j b)) ↔
      i ≠ j ∨ a = b := by
  rw [finitePauli_commute_iff_sign]
  change finitePauliConjugationSign (singlePauliAxisLabel i a) (onsiteWord j b) = 1 ↔ _
  rw [finitePauliConjugationSign_singlePauliAxisLabel]
  by_cases h : i = j
  · subst j
    by_cases hab : a = b
    · simp [onsiteWord, boolPauliConjugationSign, hab]
    · simp [onsiteWord, boolPauliConjugationSign, hab, neg_ne_self.mpr (one_ne_zero : (1 : ℂ) ≠ 0)]
  · simp [onsiteWord, boolPauliConjugationSign, h]

/-- Sites supporting at least two different onsite axes. -/
def multiAxisSites (S : Set (Fin (n + 2) × Fin 3)) : Set (Fin (n + 2)) :=
  {i | ∃ a b, (i, a) ∈ S ∧ (i, b) ∈ S ∧ a ≠ b}

/-- Exact classification of noncontextual onsite supports. -/
theorem onsiteSupport_noncontextual_iff (S : Set (Fin (n + 2) × Fin 3)) :
    PauliNoncontextual (fun i : S => finitePauliMatrix (onsiteWord i.1.1 i.1.2)) ↔
      (multiAxisSites S).Subsingleton := by
  let A := fun i : S => finitePauliMatrix (onsiteWord i.1.1 i.1.2)
  have hcomm (i j : S) : Commute (A i) (A j) ↔ i.1.1 ≠ j.1.1 ∨ i.1.2 = j.1.2 :=
    commute_onsitePauli_iff _ _ _ _
  constructor
  · intro h i hi j hj
    by_contra hij
    obtain ⟨a, a', ha, ha', haa'⟩ := hi
    obtain ⟨b, b', hb, hb', hbb'⟩ := hj
    exact not_pauliNoncontextual_of_pairs A ⟨(i, a), ha⟩ ⟨(i, a'), ha'⟩
      ⟨(j, b), hb⟩ ⟨(j, b'), hb'⟩
      ⟨fun h => ((hcomm _ _).mp h).elim (fun h => h rfl) haa',
        fun h => ((hcomm _ _).mp h).elim (fun h => h rfl) hbb',
        (hcomm _ _).mpr (Or.inl hij), (hcomm _ _).mpr (Or.inl hij)⟩ h
  · intro h i j k hi hj hk hij hik
    have hsite (x : S) : PauliNoncentral A x → x.1.1 ∈ multiAxisSites S := by
      rintro ⟨y, hy⟩
      have hxy : x.1.1 = y.1.1 := by
        by_contra hne
        exact hy ((hcomm _ _).mpr (Or.inl hne))
      have haxis : x.1.2 ≠ y.1.2 := fun he => hy ((hcomm _ _).mpr (Or.inr he))
      refine ⟨x.1.2, y.1.2, x.2, ?_, haxis⟩
      rw [hxy]
      exact y.2
    have h₁ := h (hsite i hi) (hsite j hj)
    have h₂ := h (hsite i hi) (hsite k hk)
    have h₃ := ((hcomm _ _).mp hij).resolve_left (not_not_intro h₁)
    have h₄ := ((hcomm _ _).mp hik).resolve_left (not_not_intro h₂)
    exact (hcomm _ _).mpr (Or.inr (h₃.symm.trans h₄))

/-- Active terms of the actual nearest-neighbour shell. -/
abbrev ActivePathLabels (u : PathShell n) := {l : PathLabel n // u l ≠ 0}

/-- A contextual onsite witness survives the addition of arbitrary bond terms. -/
theorem path_noncontextual_forbids_two_multiaxis_sites (u : PathShell n) :
    PauliNoncontextual (fun l : ActivePathLabels u => finitePauliMatrix (pathWord l.1)) →
      (multiAxisSites {ia | u (.inl ia) ≠ 0}).Subsingleton := by
  intro h i hi j hj
  by_contra hij
  obtain ⟨a, a', ha, ha', haa'⟩ := hi
  obtain ⟨b, b', hb, hb', hbb'⟩ := hj
  let A := fun l : ActivePathLabels u => finitePauliMatrix (pathWord l.1)
  let f (s : Fin (n + 2)) (c : Fin 3) (hc : u (.inl (s,c)) ≠ 0) :
      ActivePathLabels u := ⟨.inl (s,c), hc⟩
  exact not_pauliNoncontextual_of_pairs A (f i a ha) (f i a' ha') (f j b hb) (f j b' hb')
    ⟨fun h => ((commute_onsitePauli_iff i i a a').mp h).elim (fun h => h rfl) haa',
      fun h => ((commute_onsitePauli_iff j j b b').mp h).elim (fun h => h rfl) hbb',
      (commute_onsitePauli_iff i j a b).mpr (Or.inl hij),
      (commute_onsitePauli_iff i j a b').mpr (Or.inl hij)⟩ h

/-- The same Gaussian realization has contextual support on every open prefix
with at least two sites. Only the first two sites are needed as witnesses. -/
theorem gaussian_path_ae_contextual :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ n,
      ¬ PauliNoncontextual
        (fun l : ActivePathLabels (pathPauliDisorderShell ω n) =>
          finitePauliMatrix (pathWord l.1)) := by
  have h (k : ℕ × PathPauliDirections) :
      ∀ᵐ ω ∂pathPauliDisorderLaw, ω k ≠ 0 := by
    letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
    have hnormal : ∀ᵐ x : ℝ ∂gaussianReal 0 1, x ≠ 0 := by
      apply ae_iff.mpr
      change gaussianReal 0 1 {x : ℝ | ¬ x ≠ 0} = 0
      simpa only [not_not] using (measure_singleton (μ := gaussianReal 0 1) (0 : ℝ))
    exact (measurePreserving_eval_infinitePi
      (fun _ : ℕ × PathPauliDirections => gaussianReal 0 1) k).quasiMeasurePreserving.ae hnormal
  filter_upwards [ae_all_iff.mpr h] with ω hω
  intro n hc
  have hm := path_noncontextual_forbids_two_multiaxis_sites (pathPauliDisorderShell ω n) hc
  have member (s : Fin (n + 2)) :
      s ∈ multiAxisSites {ia | pathPauliDisorderShell ω n (.inl ia) ≠ 0} :=
    ⟨0, 1, hω (s.val, .inl 0), hω (s.val, .inl 1), Fin.zero_ne_one⟩
  exact Fin.zero_ne_one (hm (member 0) (member 1))

#print axioms onsiteSupport_noncontextual_iff
#print axioms path_noncontextual_forbids_two_multiaxis_sites
#print axioms gaussian_path_ae_contextual

end

end GaloisForLFunctions.HTGeometry
