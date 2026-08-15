import GaloisForLFunctions.HTGeometry.SymmetricPolynomialJets

/-!
# The symmetric passport multiplier

A prescribed finite normalization passport is enforced by multiplying every perturbation by a fixed
polynomial vanishing to even order on the prescribed set.  Evenness of the order makes the
multiplier invariant under both the functional equation and Schwarz reality when the prescribed set
and its jet depths are, and divisibility makes every prescribed jet of the perturbed source equal to
the original one.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-! ### Divisibility and iterated derivatives -/

theorem dvd_derivative_of_dvd_pow_succ (a : ℂ) (k : ℕ) {P : Polynomial ℂ}
    (h : (Polynomial.X - Polynomial.C a) ^ (k + 1) ∣ P) :
    (Polynomial.X - Polynomial.C a) ^ k ∣ Polynomial.derivative P := by
  obtain ⟨S, rfl⟩ := h
  rw [Polynomial.derivative_mul]
  refine dvd_add ?_ ?_
  · have h1 : (Polynomial.X - Polynomial.C a) ^ k ∣
        Polynomial.derivative ((Polynomial.X - Polynomial.C a) ^ (k + 1)) := by
      rw [Polynomial.derivative_pow, Nat.add_sub_cancel]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left dvd_rfl _) _
    exact h1.mul_right S
  · exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

theorem dvd_iterate_derivative (a : ℂ) :
    ∀ (j n : ℕ) (P : Polynomial ℂ), (Polynomial.X - Polynomial.C a) ^ (n + j) ∣ P →
      (Polynomial.X - Polynomial.C a) ^ n ∣ Polynomial.derivative^[j] P := by
  intro j
  induction j with
  | zero => intro n P h; simpa using h
  | succ j ih =>
      intro n P h
      rw [Function.iterate_succ_apply]
      refine ih n (Polynomial.derivative P) ?_
      refine dvd_derivative_of_dvd_pow_succ a (n + j) ?_
      have hexp : n + j + 1 = n + (j + 1) := by omega
      rwa [hexp]

theorem eval_iterate_derivative_eq_zero_of_dvd {a : ℂ} {n j : ℕ} (hj : j < n)
    {P : Polynomial ℂ} (h : (Polynomial.X - Polynomial.C a) ^ n ∣ P) :
    (Polynomial.derivative^[j] P).eval a = 0 := by
  have hsplit : n = (n - j) + j := by omega
  have hd : (Polynomial.X - Polynomial.C a) ^ (n - j) ∣ Polynomial.derivative^[j] P :=
    dvd_iterate_derivative a j (n - j) P (by rw [← hsplit]; exact h)
  obtain ⟨S, hS⟩ := hd
  rw [hS, Polynomial.eval_mul, Polynomial.eval_pow]
  have hne : n - j ≠ 0 := by omega
  simp [hne]

/-! ### The passport multiplier -/

/-- The symmetric passport multiplier of a prescribed finite jet passport. -/
def symPassportPoly (A : Finset ℂ) (dep : ℂ → ℕ) : Polynomial ℂ :=
  ∏ a ∈ A, (Polynomial.X - Polynomial.C a) ^ (2 * dep a)

theorem symPassportPoly_ne_zero (A : Finset ℂ) (dep : ℂ → ℕ) :
    symPassportPoly A dep ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun a _ => ?_
  exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)

theorem eval_symPassportPoly_ne_zero {A : Finset ℂ} {dep : ℂ → ℕ} {z : ℂ} (hz : z ∉ A) :
    (symPassportPoly A dep).eval z ≠ 0 := by
  rw [symPassportPoly, Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
  rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  refine pow_ne_zero _ (sub_ne_zero_of_ne ?_)
  intro hcon
  exact hz (hcon ▸ ha)

theorem dvd_symPassportPoly {A : Finset ℂ} {dep : ℂ → ℕ} {a : ℂ} (ha : a ∈ A) :
    (Polynomial.X - Polynomial.C a) ^ (2 * dep a) ∣ symPassportPoly A dep :=
  Finset.dvd_prod_of_mem _ ha

/-- **The passport multiplier fixes every prescribed jet.** -/
theorem eval_iterate_derivative_symPassportPoly_mul {A : Finset ℂ} {dep : ℂ → ℕ} {a : ℂ}
    (ha : a ∈ A) {j : ℕ} (hj : j < dep a) (q : Polynomial ℂ) :
    (Polynomial.derivative^[j] (symPassportPoly A dep * q)).eval a = 0 := by
  refine eval_iterate_derivative_eq_zero_of_dvd (n := 2 * dep a) (by omega) ?_
  exact Dvd.dvd.mul_right (dvd_symPassportPoly ha) q

/-! ### Symmetry of the passport multiplier -/

theorem reflectPoly_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    reflectPoly (∏ i ∈ s, f i) = ∏ i ∈ s, reflectPoly (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflectPoly]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, reflectPoly, Polynomial.mul_comp,
        ← reflectPoly, ← reflectPoly, ih]

theorem conjPoly_prod {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) :
    conjPoly (∏ i ∈ s, f i) = ∏ i ∈ s, conjPoly (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [conjPoly]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, conjPoly, Polynomial.map_mul,
        ← conjPoly, ← conjPoly, ih]

theorem reflectPoly_X_sub_C_pow (a : ℂ) (n : ℕ) :
    reflectPoly ((Polynomial.X - Polynomial.C a) ^ (2 * n))
      = (Polynomial.X - Polynomial.C (1 - a)) ^ (2 * n) := by
  rw [reflectPoly, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
    Polynomial.C_comp]
  have hstep : ((1 : Polynomial ℂ) - Polynomial.X) - Polynomial.C a
      = -(Polynomial.X - Polynomial.C (1 - a)) := by
    rw [Polynomial.C_sub, Polynomial.C_1]
    ring
  rw [hstep, neg_pow]
  rw [show (-1 : Polynomial ℂ) ^ (2 * n) = 1 from by
    rw [pow_mul]
    norm_num]
  ring

theorem conjPoly_X_sub_C_pow (a : ℂ) (n : ℕ) :
    conjPoly ((Polynomial.X - Polynomial.C a) ^ n)
      = (Polynomial.X - Polynomial.C ((starRingEnd ℂ) a)) ^ n := by
  rw [conjPoly, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

theorem reflectPoly_symPassportPoly {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA : ∀ a ∈ A, 1 - a ∈ A) (hdep : ∀ a ∈ A, dep (1 - a) = dep a) :
    reflectPoly (symPassportPoly A dep) = symPassportPoly A dep := by
  classical
  rw [symPassportPoly, reflectPoly_prod]
  rw [Finset.prod_congr rfl (fun a _ => reflectPoly_X_sub_C_pow a (dep a))]
  refine Finset.prod_nbij' (fun a => 1 - a) (fun b => 1 - b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact hA a ha
  · intro b hb
    exact hA b hb
  · intro a _
    ring
  · intro b _
    ring
  · intro a ha
    rw [hdep a ha]

theorem conjPoly_symPassportPoly {A : Finset ℂ} {dep : ℂ → ℕ}
    (hA : ∀ a ∈ A, (starRingEnd ℂ) a ∈ A) (hdep : ∀ a ∈ A, dep ((starRingEnd ℂ) a) = dep a) :
    conjPoly (symPassportPoly A dep) = symPassportPoly A dep := by
  classical
  rw [symPassportPoly, conjPoly_prod]
  rw [Finset.prod_congr rfl (fun a _ => conjPoly_X_sub_C_pow a (2 * dep a))]
  refine Finset.prod_nbij' (fun a => (starRingEnd ℂ) a) (fun b => (starRingEnd ℂ) b) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    exact hA a ha
  · intro b hb
    exact hA b hb
  · intro a _
    exact Complex.conj_conj a
  · intro b _
    exact Complex.conj_conj b
  · intro a ha
    rw [hdep a ha]

end

end GaloisForLFunctions.HTGeometry
