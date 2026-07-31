import GaloisForLFunctions.HTGeometry.Hypertranscendence
import GaloisForLFunctions.HTGeometry.LinearIndependentMinorCertificate
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentCoefficient

/-!
# The pole-jet certificate for hypertranscendence

An algebraic differential equation for `f` is a vanishing `ℂ`-linear combination of the differential
monomials `z ^ m₀ * ∏ (f⁽ʲ⁾ z) ^ mⱼ₊₁`.  If `f` is meromorphic at `a`, each such monomial is
meromorphic at `a`, so the Laurent transform at `a` is a `ℂ`-linear injection on their germs: a
relation among the monomials is exactly a relation among their rows of Laurent coefficients.
Independence of finitely many columns of a coordinate matrix is in turn certified by a single
nonvanishing square minor.  Hypertranscendence near `a` is therefore equivalent to the existence, at
every jet order and for every finite set of differential monomials, of one nonzero determinant built
from Laurent coefficients at `a`.

* `jetVector`, `jetMonomial` — the jet coordinates `(z, f z, …, f⁽ⁿ⁾ z)` and their monomials.
* `DifferentiallyAlgebraicNear`, `HypertranscendentalNear` — the local forms of the notions, taken
  on a punctured neighbourhood, where the derivatives of a meromorphic function are honest.
* `hypertranscendentalNear_iff_forall_linearIndependent_jetLaurentRow` — hypertranscendence near `a`
  is linear independence of the Laurent rows.
* `hypertranscendentalNear_iff_forall_exists_jetLaurentMinor_det_ne_zero` — the finite determinant
  certificate.
* `hypertranscendental_of_hypertranscendentalNear` — the certificate implies hypertranscendence in
  the global sense.
* `differentiallyAlgebraicNear_iff_of_isPreconnected` — on a preconnected domain of meromorphy the
  local notion, hence the certificate, does not depend on the chosen point.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped BigOperators

/-- The jet vector `(z, f z, f' z, …, f⁽ⁿ⁾ z)`, in the variable order used by
`DifferentiallyAlgebraic`: coordinate `0` is the point, coordinate `j + 1` is `f⁽ʲ⁾`. -/
noncomputable def jetVector (f : ℂ → ℂ) (n : ℕ) (z : ℂ) : Fin (n + 2) → ℂ :=
  Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z

/-- The differential monomial `z ^ m 0 * ∏ⱼ (f⁽ʲ⁾ z) ^ m (j + 1)` attached to an exponent vector. -/
noncomputable def jetMonomial (f : ℂ → ℂ) (n : ℕ) (m : Fin (n + 2) →₀ ℕ) : ℂ → ℂ :=
  fun z => ∏ i ∈ m.support, jetVector f n z i ^ m i

/-- The row of Laurent coefficients at `a` of a differential monomial. -/
noncomputable def jetLaurentRow (f : ℂ → ℂ) (a : ℂ) (n : ℕ) (m : Fin (n + 2) →₀ ℕ) : ℤ → ℂ :=
  laurentCoeff (jetMonomial f n m) a

/-- `f` satisfies an algebraic differential equation on a punctured neighbourhood of `a`. -/
def DifferentiallyAlgebraicNear (f : ℂ → ℂ) (a : ℂ) : Prop :=
  ∃ (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ), P ≠ 0 ∧
    (fun z => MvPolynomial.eval (jetVector f n z) P) =ᶠ[𝓝[≠] a] 0

/-- `f` satisfies no algebraic differential equation on any punctured neighbourhood of `a`. -/
def HypertranscendentalNear (f : ℂ → ℂ) (a : ℂ) : Prop := ¬ DifferentiallyAlgebraicNear f a

/-! ### Meromorphy of the differential monomials -/

/-- Each jet coordinate of a function meromorphic at `a` is meromorphic at `a`. -/
theorem meromorphicAt_jetVector_coord {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (n : ℕ)
    (i : Fin (n + 2)) : MeromorphicAt (fun z => jetVector f n z i) a := by
  induction i using Fin.cases with
  | zero =>
      have : (fun z : ℂ => jetVector f n z 0) = fun z : ℂ => z := by
        funext z; simp [jetVector]
      rw [this]
      exact (analyticAt_id (𝕜 := ℂ) (z := a)).meromorphicAt
  | succ j =>
      have hcoord : (fun z : ℂ => jetVector f n z j.succ)
          = fun z : ℂ => iteratedDeriv (j : ℕ) f z := by
        funext z; simp [jetVector]
      rw [hcoord]
      have hd : MeromorphicAt (deriv^[(j : ℕ)] f) a := hf.iterated_deriv
      rwa [← iteratedDeriv_eq_iterate] at hd

/-- Differential monomials of a function meromorphic at `a` are meromorphic at `a`. -/
theorem meromorphicAt_jetMonomial {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (n : ℕ)
    (m : Fin (n + 2) →₀ ℕ) : MeromorphicAt (jetMonomial f n m) a := by
  refine MeromorphicAt.fun_prod ?_
  intro i _
  exact (meromorphicAt_jetVector_coord hf n i).fun_pow (m i)

/-- The evaluation of an algebraic differential polynomial at the jets of a function meromorphic at
`a` is meromorphic at `a`. -/
theorem meromorphicAt_eval_jetVector {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (n : ℕ)
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    MeromorphicAt (fun z => MvPolynomial.eval (jetVector f n z) P) a := by
  have hrw : (fun z => MvPolynomial.eval (jetVector f n z) P)
      = fun z => ∑ m ∈ P.support, MvPolynomial.coeff m P * jetMonomial f n m z := by
    funext z
    rw [MvPolynomial.eval_eq]
    rfl
  rw [hrw]
  refine MeromorphicAt.fun_sum ?_
  intro m _
  exact MeromorphicAt.fun_mul (MeromorphicAt.const _ a) (meromorphicAt_jetMonomial hf n m)

/-! ### Algebraic differential relations as linear relations among the monomials -/

theorem eval_jetVector_eq_sum (f : ℂ → ℂ) (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (z : ℂ) :
    MvPolynomial.eval (jetVector f n z) P
      = ∑ m ∈ P.support, MvPolynomial.coeff m P * jetMonomial f n m z := by
  rw [MvPolynomial.eval_eq]
  rfl

theorem eval_jetVector_sum_monomial (f : ℂ → ℂ) (n : ℕ) (s : Finset (Fin (n + 2) →₀ ℕ))
    (g : (Fin (n + 2) →₀ ℕ) → ℂ) (z : ℂ) :
    MvPolynomial.eval (jetVector f n z) (∑ m ∈ s, MvPolynomial.monomial m (g m))
      = ∑ m ∈ s, g m * jetMonomial f n m z := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.eval_monomial]
  rfl

theorem coeff_sum_monomial {n : ℕ} (s : Finset (Fin (n + 2) →₀ ℕ))
    (g : (Fin (n + 2) →₀ ℕ) → ℂ) {m₀ : Fin (n + 2) →₀ ℕ} (hm₀ : m₀ ∈ s) :
    MvPolynomial.coeff m₀ (∑ m ∈ s, MvPolynomial.monomial m (g m)) = g m₀ := by
  classical
  rw [MvPolynomial.coeff_sum]
  simp [MvPolynomial.coeff_monomial, Finset.sum_ite_eq' s m₀ g, hm₀]

/-! ### The Laurent bridge -/

/-- A finite `ℂ`-linear relation among differential monomials holds on a punctured neighbourhood of
`a` exactly when the same relation holds among their rows of Laurent coefficients. -/
theorem eventuallyEq_zero_iff_forall_jetLaurentRow {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a)
    (n : ℕ) (s : Finset (Fin (n + 2) →₀ ℕ)) (g : (Fin (n + 2) →₀ ℕ) → ℂ) :
    (fun z => ∑ m ∈ s, g m * jetMonomial f n m z) =ᶠ[𝓝[≠] a] 0
      ↔ ∀ ℓ : ℤ, ∑ m ∈ s, g m * jetLaurentRow f a n m ℓ = 0 := by
  have hmero : MeromorphicAt (fun z => ∑ m ∈ s, g m * jetMonomial f n m z) a := by
    refine MeromorphicAt.fun_sum ?_
    intro m _
    exact MeromorphicAt.fun_mul (MeromorphicAt.const _ a) (meromorphicAt_jetMonomial hf n m)
  have hlin : ∀ ℓ : ℤ,
      laurentCoeff (fun z => ∑ m ∈ s, g m * jetMonomial f n m z) a ℓ
        = ∑ m ∈ s, g m * jetLaurentRow f a n m ℓ := fun ℓ =>
    laurentCoeff_sum s (fun m => jetMonomial f n m) g a ℓ
      (fun m _ => meromorphicAt_jetMonomial hf n m)
  rw [eventuallyEq_zero_nhdsNE_iff_forall_laurentCoeff_eq_zero hmero]
  exact ⟨fun h ℓ => (hlin ℓ) ▸ h ℓ, fun h ℓ => (hlin ℓ).trans (h ℓ)⟩

/-! ### The certificate -/

/-- **Hypertranscendence near `a` is linear independence of the Laurent rows.** -/
theorem hypertranscendentalNear_iff_forall_linearIndependent_jetLaurentRow {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) :
    HypertranscendentalNear f a ↔ ∀ n : ℕ, LinearIndependent ℂ (jetLaurentRow f a n) := by
  classical
  constructor
  · intro hHT n
    rw [linearIndependent_iff']
    intro s g hg m₀ hm₀
    by_contra hne
    refine hHT ⟨n, ∑ m ∈ s, MvPolynomial.monomial m (g m), ?_, ?_⟩
    · intro hP
      apply hne
      rw [← coeff_sum_monomial s g hm₀, hP, MvPolynomial.coeff_zero]
    · have hrow : ∀ ℓ : ℤ, ∑ m ∈ s, g m * jetLaurentRow f a n m ℓ = 0 := by
        intro ℓ
        have := congrFun hg ℓ
        simpa [Finset.sum_apply] using this
      have hzero := (eventuallyEq_zero_iff_forall_jetLaurentRow hf n s g).mpr hrow
      filter_upwards [hzero] with z hz
      rw [eval_jetVector_sum_monomial]
      exact hz
  · rintro hLI ⟨n, P, hP, hrel⟩
    have hrow : ∀ ℓ : ℤ, ∑ m ∈ P.support, MvPolynomial.coeff m P * jetLaurentRow f a n m ℓ = 0 := by
      refine (eventuallyEq_zero_iff_forall_jetLaurentRow hf n P.support
        (fun m => MvPolynomial.coeff m P)).mp ?_
      filter_upwards [hrel] with z hz
      rw [← eval_jetVector_eq_sum]
      exact hz
    have hsum : ∑ m ∈ P.support, (MvPolynomial.coeff m P) • jetLaurentRow f a n m = 0 := by
      funext ℓ
      simpa [Finset.sum_apply] using hrow ℓ
    obtain ⟨m₀, hm₀⟩ := MvPolynomial.ne_zero_iff.mp hP
    exact hm₀ ((linearIndependent_iff'.mp (hLI n)) P.support
      (fun m => MvPolynomial.coeff m P) hsum m₀ (MvPolynomial.mem_support_iff.mpr hm₀))

/-- **The finite pole-jet determinant certificate.**  `f` is hypertranscendental near `a` exactly
when, at every jet order `n` and for every finite family of differential monomials, some square
matrix of Laurent coefficients at `a` has nonzero determinant. -/
theorem hypertranscendentalNear_iff_forall_exists_jetLaurentMinor_det_ne_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a) :
    HypertranscendentalNear f a ↔
      ∀ (n : ℕ) (s : Finset (Fin (n + 2) →₀ ℕ)),
        ∃ φ : {m // m ∈ s} → ℤ,
          (coordinateMinor
            (fun m : {x // x ∈ s} => jetLaurentRow f a n (m : Fin (n + 2) →₀ ℕ)) φ).det ≠ 0 := by
  classical
  rw [hypertranscendentalNear_iff_forall_linearIndependent_jetLaurentRow hf]
  constructor
  · intro h n
    exact (linearIndependent_iff_forall_finset_exists_coordinateMinor_det_ne_zero
      (jetLaurentRow f a n)).mp (h n)
  · intro h n
    exact (linearIndependent_iff_forall_finset_exists_coordinateMinor_det_ne_zero
      (jetLaurentRow f a n)).mpr (h n)

/-- The bounded column family of a fixed complexity: jets to order `r`, total jet degree at most
`D`, and powers of the variable at most `E`. -/
def BoundedJetExponent (r D E : ℕ) (m : Fin (r + 2) →₀ ℕ) : Prop :=
  (∑ j : Fin (r + 1), m j.succ) ≤ D ∧ m 0 ≤ E

/-- Every finite family of differential monomials of jet order `r` has a bounded complexity. -/
theorem exists_boundedJetExponent {r : ℕ} (s : Finset (Fin (r + 2) →₀ ℕ)) :
    ∃ D E : ℕ, ∀ m ∈ s, BoundedJetExponent r D E m := by
  refine ⟨s.sup fun m => ∑ j : Fin (r + 1), m j.succ, s.sup fun m => m 0, fun m hm => ?_⟩
  exact ⟨Finset.le_sup (f := fun m : Fin (r + 2) →₀ ℕ => ∑ j : Fin (r + 1), m j.succ) hm,
    Finset.le_sup (f := fun m : Fin (r + 2) →₀ ℕ => m 0) hm⟩

/-- **The certificate at bounded complexity.**  `f` is hypertranscendental near `a` exactly when, at
every jet order and every degree bound, each family of differential monomials of that complexity
carries a square matrix of Laurent coefficients at `a` with nonzero determinant. -/
theorem hypertranscendentalNear_iff_forall_bounded_exists_jetLaurentMinor_det_ne_zero
    {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    HypertranscendentalNear f a ↔
      ∀ (r D E : ℕ) (s : Finset (Fin (r + 2) →₀ ℕ)),
        (∀ m ∈ s, BoundedJetExponent r D E m) →
        ∃ φ : {m // m ∈ s} → ℤ,
          (coordinateMinor
            (fun m : {x // x ∈ s} => jetLaurentRow f a r (m : Fin (r + 2) →₀ ℕ)) φ).det ≠ 0 := by
  rw [hypertranscendentalNear_iff_forall_exists_jetLaurentMinor_det_ne_zero hf]
  constructor
  · intro h r D E s _
    exact h r s
  · intro h n s
    obtain ⟨D, E, hDE⟩ := exists_boundedJetExponent s
    exact h n D E s hDE

/-! ### Comparison with the global notion -/

/-- A global algebraic differential equation is in particular a local one. -/
theorem differentiallyAlgebraicNear_of_differentiallyAlgebraic {f : ℂ → ℂ} (a : ℂ)
    (h : DifferentiallyAlgebraic f) : DifferentiallyAlgebraicNear f a := by
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, P, hP, ?_⟩
  filter_upwards with z
  exact hrel z

/-- **The pole-jet certificate implies hypertranscendence.** -/
theorem hypertranscendental_of_hypertranscendentalNear {f : ℂ → ℂ} (a : ℂ)
    (h : HypertranscendentalNear f a) : Hypertranscendental f := fun hDA =>
  h (differentiallyAlgebraicNear_of_differentiallyAlgebraic a hDA)

/-- **Hypertranscendence from one pole.**  A nonvanishing Laurent minor at every jet order and every
finite family of differential monomials, at a single point of meromorphy, already certifies that `f`
satisfies no algebraic differential equation. -/
theorem hypertranscendental_of_forall_exists_jetLaurentMinor_det_ne_zero {f : ℂ → ℂ} {a : ℂ}
    (hf : MeromorphicAt f a)
    (h : ∀ (n : ℕ) (s : Finset (Fin (n + 2) →₀ ℕ)),
      ∃ φ : {m // m ∈ s} → ℤ,
        (coordinateMinor
          (fun m : {x // x ∈ s} => jetLaurentRow f a n (m : Fin (n + 2) →₀ ℕ)) φ).det ≠ 0) :
    Hypertranscendental f :=
  hypertranscendental_of_hypertranscendentalNear a
    ((hypertranscendentalNear_iff_forall_exists_jetLaurentMinor_det_ne_zero hf).mpr h)

/-! ### Independence of the chosen point -/

/-- **The local notion does not depend on the point.**  On a preconnected set of meromorphy, an
algebraic differential relation valid near one point is valid near every point; hence the pole-jet
certificate may be read at any point of the domain. -/
theorem differentiallyAlgebraicNear_iff_of_isPreconnected {f : ℂ → ℂ} {U : Set ℂ}
    (hf : MeromorphicOn f U) (hU : IsPreconnected U) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    DifferentiallyAlgebraicNear f a ↔ DifferentiallyAlgebraicNear f b := by
  have key : ∀ x y : ℂ, x ∈ U → y ∈ U →
      DifferentiallyAlgebraicNear f x → DifferentiallyAlgebraicNear f y := by
    rintro x y hx hy ⟨n, P, hP, hrel⟩
    refine ⟨n, P, hP, ?_⟩
    have hmero : MeromorphicOn (fun z => MvPolynomial.eval (jetVector f n z) P) U :=
      fun w hw => meromorphicAt_eval_jetVector (hf w hw) n P
    have htopx : meromorphicOrderAt (fun z => MvPolynomial.eval (jetVector f n z) P) x = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr hrel
    by_contra hcon
    have hney : meromorphicOrderAt (fun z => MvPolynomial.eval (jetVector f n z) P) y ≠ ⊤ :=
      fun hc => hcon (meromorphicOrderAt_eq_top_iff.mp hc)
    exact absurd
      (hmero.meromorphicOrderAt_ne_top_of_isPreconnected hU hy hx hney) (by rw [htopx]; simp)
  exact ⟨key a b ha hb, key b a hb ha⟩

end GaloisForLFunctions.HTGeometry
