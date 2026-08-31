import GaloisForLFunctions.HTGeometry.LaurentLeadingDeterminant

/-!
# Boundary coefficients as a graded calculus

`HasLead f d c` records that a Laurent series vanishes below degree `d` and has coefficient `c`
there.  It is closed under sums at a common degree, under products with degrees adding, and it
weakens to any smaller degree with boundary coefficient zero.  So the boundary coefficient behaves
like a graded ring homomorphism, which is what makes a Newton-corner degeneration a finite
computation: every entry of the observability Jacobian is built from the coordinates and the
branches by sums and products, so its boundary coefficient is the corresponding model entry.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F]

/-- `f` vanishes below degree `d` and has coefficient `c` there. -/
def HasLead (f : LaurentSeries F) (d : ℤ) (c : F) : Prop :=
  (∀ k < d, f.coeff k = 0) ∧ f.coeff d = c

theorem HasLead.vanishing {f : LaurentSeries F} {d : ℤ} {c : F} (h : HasLead f d c) :
    ∀ k < d, f.coeff k = 0 := h.1

theorem HasLead.coeff {f : LaurentSeries F} {d : ℤ} {c : F} (h : HasLead f d c) :
    f.coeff d = c := h.2

theorem hasLead_zero (d : ℤ) : HasLead (0 : LaurentSeries F) d 0 :=
  ⟨fun _ _ => rfl, rfl⟩

theorem hasLead_one : HasLead (1 : LaurentSeries F) 0 1 :=
  ⟨fun k hk => by rw [HahnSeries.coeff_one, if_neg (by omega)],
    by rw [HahnSeries.coeff_one, if_pos rfl]⟩

theorem HasLead.mono {f : LaurentSeries F} {d e : ℤ} {c : F} (h : HasLead f d c) (hed : e < d) :
    HasLead f e 0 :=
  ⟨fun k hk => h.1 k (by omega), h.1 e hed⟩

theorem HasLead.add {f g : LaurentSeries F} {d : ℤ} {c c' : F}
    (hf : HasLead f d c) (hg : HasLead g d c') : HasLead (f + g) d (c + c') :=
  ⟨fun k hk => by rw [HahnSeries.coeff_add, hf.1 k hk, hg.1 k hk, add_zero],
    by rw [HahnSeries.coeff_add, hf.2, hg.2]⟩

theorem HasLead.neg {f : LaurentSeries F} {d : ℤ} {c : F} (hf : HasLead f d c) :
    HasLead (-f) d (-c) :=
  ⟨fun k hk => by rw [HahnSeries.coeff_neg, hf.1 k hk, neg_zero],
    by rw [HahnSeries.coeff_neg, hf.2]⟩

theorem HasLead.sub {f g : LaurentSeries F} {d : ℤ} {c c' : F}
    (hf : HasLead f d c) (hg : HasLead g d c') : HasLead (f - g) d (c - c') := by
  have h := hf.add hg.neg
  rw [← sub_eq_add_neg] at h
  rw [← sub_eq_add_neg] at h
  exact h

theorem HasLead.mul {f g : LaurentSeries F} {d e : ℤ} {c c' : F}
    (hf : HasLead f d c) (hg : HasLead g e c') : HasLead (f * g) (d + e) (c * c') :=
  ⟨coeff_mul_eq_zero_of_lt hf.1 hg.1,
    by rw [coeff_mul_of_vanishing_below hf.1 hg.1, hf.2, hg.2]⟩

theorem HasLead.pow {f : LaurentSeries F} {d : ℤ} {c : F} (hf : HasLead f d c) :
    ∀ m : ℕ, HasLead (f ^ m) (m * d) (c ^ m)
  | 0 => by simpa using hasLead_one
  | (m + 1) => by
      have h := (hf.pow m).mul hf
      have hd : ((m : ℤ) * d + d) = ((m + 1 : ℕ) : ℤ) * d := by push_cast; ring
      rw [hd] at h
      rw [pow_succ, pow_succ]
      exact h

/-- **The leading determinant test, in `HasLead` form.** -/
theorem det_ne_zero_of_hasLead {n : ℕ} (M : Matrix (Fin n) (Fin n) (LaurentSeries F))
    (a b : Fin n → ℤ) (L : Matrix (Fin n) (Fin n) F)
    (hM : ∀ i j, HasLead (M i j) (a i + b j) (L i j)) (hL : L.det ≠ 0) :
    M.det ≠ 0 := by
  refine det_ne_zero_of_leading_det_ne_zero M a b (fun i j => (hM i j).1) ?_
  have hLeq : (Matrix.of fun i j => (M i j).coeff (a i + b j)) = L := by
    funext i j
    exact (hM i j).2
  rw [hLeq]
  exact hL

end GaloisForLFunctions.HTGeometry
