import GaloisForLFunctions.HTGeometry.SteinbergWeylInverseConjugation

/-!
# The Steinberg relation from a rank-three Bruhat calculation

For units `r, s` with `r + s = 1`, the classical Bruhat word calculation proves

```text
w_ij(r) w_ij(-1) w_ij(s) = w_ij(rs).
```

The proof needs a third index to establish the exact orientation identity
`w_ij(r) w_ji(r⁻¹) = 1`; it is not merely an equality modulo `K₂`.  Appending
`w_ij(-1)` gives multiplicativity of the torus at complementary units.  Running
the same result in the opposite order makes those two torus elements commute,
so the defining torus cocycle is trivial: `{r, s} = 1`.

This is the rank-three core of Matsumoto's Steinberg relation, formalized directly
from the Steinberg presentation.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

omit [DecidableEq n] [Fintype n] in
/-- Moving an opposite-root generator past a Weyl word. -/
theorem steinbergWeyl_mul_transpose {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r : Rˣ) (b : R) :
    steinbergWeyl hij r * steinbergX (Ne.symm hij) b
      = steinbergX hij (-((r : R) * b * (r : R))) * steinbergWeyl hij r := by
  calc steinbergWeyl hij r * steinbergX (Ne.symm hij) b
      = (steinbergWeyl hij r * steinbergX (Ne.symm hij) b * (steinbergWeyl hij r)⁻¹)
        * steinbergWeyl hij r := by group
    _ = steinbergX hij (-((r : R) * b * (r : R))) * steinbergWeyl hij r := by
      rw [steinbergWeyl_conj_transpose hij hik hjk]

omit [DecidableEq n] [Fintype n] in
/-- Moving an opposite-root generator across a Weyl word from the left. -/
theorem steinbergTranspose_mul_weyl {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r : Rˣ) (b : R) :
    steinbergX (Ne.symm hij) b * steinbergWeyl hij r
      = steinbergWeyl hij r * steinbergX hij (-((r : R) * b * (r : R))) := by
  calc steinbergX (Ne.symm hij) b * steinbergWeyl hij r
      = steinbergWeyl hij r
        * ((steinbergWeyl hij r)⁻¹ * steinbergX (Ne.symm hij) b * steinbergWeyl hij r) := by group
    _ = steinbergWeyl hij r * steinbergX hij (-((r : R) * b * (r : R))) := by
      rw [steinbergWeyl_inv_conj_transpose hij hik hjk]

omit [DecidableEq n] [Fintype n] in
/-- **Exact Weyl orientation relation** (Weibel, Exercise 5.8(e)). -/
theorem steinbergWeyl_reverse_mul {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r : Rˣ) :
    steinbergWeyl hij r * steinbergWeyl (Ne.symm hij) r⁻¹ = 1 := by
  have hconj := steinbergWeyl_conj_transpose hij hik hjk r (((r⁻¹ : Rˣ)) : R)
  have hval : -((r : R) * (((r⁻¹ : Rˣ)) : R) * (r : R)) = -((r : R) : R) := by
    have hunit : (r : R) * (((r⁻¹ : Rˣ)) : R) = 1 := r.mul_inv
    rw [show (r : R) * (((r⁻¹ : Rˣ)) : R) * (r : R)
      = ((r : R) * (((r⁻¹ : Rˣ)) : R)) * (r : R) by ring, hunit, one_mul]
  rw [hval] at hconj
  have hmove : steinbergWeyl hij r * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)
      = steinbergX hij (-((r : R) : R)) * steinbergWeyl hij r := by
    calc steinbergWeyl hij r * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)
        = (steinbergWeyl hij r * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)
          * (steinbergWeyl hij r)⁻¹) * steinbergWeyl hij r := by group
      _ = steinbergX hij (-((r : R) : R)) * steinbergWeyl hij r := by rw [hconj]
  have hinv : (((r⁻¹ : Rˣ)⁻¹ : Rˣ) : R) = ((r : R) : R) := by simp
  have hfirst : steinbergWeyl hij r * steinbergX hij (-((r : R) : R))
      = steinbergX hij ((r : R) : R) * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R)) := by
    rw [steinbergWeyl]
    calc steinbergX hij ((r : R) : R) * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
          * steinbergX hij ((r : R) : R) * steinbergX hij (-((r : R) : R))
        = steinbergX hij ((r : R) : R) * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
          * (steinbergX hij ((r : R) : R) * steinbergX hij (-((r : R) : R))) := by group
      _ = steinbergX hij ((r : R) : R) * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R)) := by
        rw [steinbergX_mul, add_neg_cancel, steinbergX_zero, mul_one]
  have hrev : steinbergWeyl (Ne.symm hij) r⁻¹
      = steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)
        * steinbergX hij (-((r : R) : R))
        * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R) := by
    rw [steinbergWeyl, hinv]
  rw [hrev]
  calc (steinbergX hij ((r : R) : R) * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
        * steinbergX hij ((r : R) : R))
      * (steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)
        * steinbergX hij (-((r : R) : R))
        * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R))
      = (steinbergWeyl hij r * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R))
        * steinbergX hij (-((r : R) : R))
        * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R) := by
          rw [steinbergWeyl]
          group
    _ = steinbergX hij (-((r : R) : R))
        * (steinbergWeyl hij r * steinbergX hij (-((r : R) : R)))
        * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R) := by rw [hmove]; group
    _ = steinbergX hij (-((r : R) : R))
        * (steinbergX hij ((r : R) : R)
          * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R)))
        * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R) := by rw [hfirst]
    _ = 1 := by
      calc steinbergX hij (-((r : R) : R)) * steinbergX hij ((r : R) : R)
            * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
            * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)
          = (steinbergX hij (-((r : R) : R)) * steinbergX hij ((r : R) : R))
            * (steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
              * steinbergX (Ne.symm hij) (((r⁻¹ : Rˣ)) : R)) := by group
        _ = 1 := by
          rw [steinbergX_mul, neg_add_cancel, steinbergX_zero,
            steinbergX_mul, neg_add_cancel, steinbergX_zero, one_mul]

omit [DecidableEq n] [Fintype n] in
/-- The reverse orientation form of `steinbergWeyl_reverse_mul`. -/
theorem steinbergWeyl_reverse {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r : Rˣ) :
    steinbergWeyl hij r = steinbergWeyl (Ne.symm hij) (-r⁻¹) := by
  calc steinbergWeyl hij r = (steinbergWeyl (Ne.symm hij) r⁻¹)⁻¹ :=
      eq_inv_of_mul_eq_one_left (steinbergWeyl_reverse_mul hij hik hjk r)
    _ = steinbergWeyl (Ne.symm hij) (-r⁻¹) :=
      (steinbergWeyl_neg (Ne.symm hij) r⁻¹).symm

omit [DecidableEq n] [Fintype n] in
/-- **Matsumoto's complementary-unit Weyl identity.** -/
theorem steinbergWeyl_product_of_add_one {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (r s : Rˣ) (hsum : (r : R) + (s : R) = 1) :
    steinbergWeyl hij r * steinbergWeyl hij (-1) * steinbergWeyl hij s
      = steinbergWeyl hij (r * s) := by
  have hprod := steinbergWeyl_reverse_mul hij hik hjk (-1 : Rˣ)
  have hnegprod : steinbergWeyl hij (-1 : Rˣ) * steinbergWeyl (Ne.symm hij) (-1 : Rˣ) = 1 := by
    simpa using hprod
  have hneg : steinbergWeyl hij (-1 : Rˣ) = steinbergWeyl (Ne.symm hij) (1 : Rˣ) := by
    calc steinbergWeyl hij (-1 : Rˣ)
        = (steinbergWeyl (Ne.symm hij) (-1 : Rˣ))⁻¹ := eq_inv_of_mul_eq_one_left hnegprod
      _ = steinbergWeyl (Ne.symm hij) (1 : Rˣ) := by
        rw [← steinbergWeyl_neg]
        norm_num
  have hrr : -((r : R) * (1 : R) * (r : R)) = -((r : R) * (r : R)) := by ring
  have hss : -((s : R) * (1 : R) * (s : R)) = -((s : R) * (s : R)) := by ring
  have hr0 : -((r : R) * (r : R)) + (r : R) = (r : R) * (s : R) := by
    calc -((r : R) * (r : R)) + (r : R) = (r : R) * (1 - (r : R)) := by ring
      _ = (r : R) * (s : R) := by rw [← hsum]; ring
  have hmid0 : (r : R) + (-1 : R) + (s : R) = 0 := by
    rw [show (r : R) + (-1 : R) + (s : R) = (r : R) + (s : R) - 1 by ring, hsum]
    exact sub_self 1
  have hs0 : (s : R) + -((s : R) * (s : R)) = (r : R) * (s : R) := by
    calc (s : R) + -((s : R) * (s : R)) = (s : R) * (1 - (s : R)) := by ring
      _ = (s : R) * (r : R) := by rw [← hsum]; ring
      _ = (r : R) * (s : R) := by ring
  have hri : (r : R) * (((r⁻¹ : Rˣ)) : R) = 1 := r.mul_inv
  have hsi : (s : R) * (((s⁻¹ : Rˣ)) : R) = 1 := s.mul_inv
  have hinv : (((r⁻¹ : Rˣ)) : R) + (((s⁻¹ : Rˣ)) : R) = (((r * s)⁻¹ : Rˣ) : R) := by
    calc (((r⁻¹ : Rˣ)) : R) + (((s⁻¹ : Rˣ)) : R)
        = (((r⁻¹ : Rˣ)) : R) * ((s : R) * (((s⁻¹ : Rˣ)) : R))
          + (((s⁻¹ : Rˣ)) : R) * ((r : R) * (((r⁻¹ : Rˣ)) : R)) := by
            rw [hsi, hri, mul_one, mul_one]
      _ = ((s : R) + (r : R)) * (((s⁻¹ : Rˣ)) : R) * (((r⁻¹ : Rˣ)) : R) := by ring
      _ = (((s⁻¹ : Rˣ)) : R) * (((r⁻¹ : Rˣ)) : R) := by
        rw [show (s : R) + (r : R) = 1 by rw [add_comm, hsum], one_mul]
      _ = (((r * s)⁻¹ : Rˣ) : R) := by
        rw [mul_inv, Units.val_mul]
        ring
  have hfirst : steinbergX hij (-((r : R) * (r : R))) * steinbergX hij (r : R)
      = steinbergX hij ((r : R) * (s : R)) := by rw [steinbergX_mul, hr0]
  have hmiddle : steinbergX hij (r : R) * steinbergX hij (-1 : R) * steinbergX hij (s : R) = 1 := by
    calc steinbergX hij (r : R) * steinbergX hij (-1 : R) * steinbergX hij (s : R)
        = (steinbergX hij (r : R) * steinbergX hij (-1 : R)) * steinbergX hij (s : R) := by group
      _ = steinbergX hij ((r : R) + (-1 : R)) * steinbergX hij (s : R) := by rw [steinbergX_mul]
      _ = steinbergX hij ((r : R) + (-1 : R) + (s : R)) := by rw [steinbergX_mul]
      _ = 1 := by rw [hmid0, steinbergX_zero]
  have hlast : steinbergX hij (s : R) * steinbergX hij (-((s : R) * (s : R)))
      = steinbergX hij ((r : R) * (s : R)) := by rw [steinbergX_mul, hs0]
  rw [hneg, steinbergWeyl]
  calc steinbergWeyl hij r
        * (steinbergX (Ne.symm hij) (1 : R) * steinbergX hij (-1 : R)
          * steinbergX (Ne.symm hij) (1 : R))
        * steinbergWeyl hij s
      = (steinbergWeyl hij r * steinbergX (Ne.symm hij) (1 : R)) * steinbergX hij (-1 : R)
        * (steinbergX (Ne.symm hij) (1 : R) * steinbergWeyl hij s) := by group
    _ = (steinbergX hij (-((r : R) * (r : R))) * steinbergWeyl hij r)
        * steinbergX hij (-1 : R)
        * (steinbergWeyl hij s * steinbergX hij (-((s : R) * (s : R)))) := by
        rw [steinbergWeyl_mul_transpose hij hik hjk r 1,
          steinbergTranspose_mul_weyl hij hik hjk s 1, hrr, hss]
    _ = steinbergX hij (-((r : R) * (r : R)))
        * (steinbergX hij (r : R) * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
          * steinbergX hij (r : R))
        * steinbergX hij (-1 : R)
        * (steinbergX hij (s : R) * steinbergX (Ne.symm hij) (-(((s⁻¹ : Rˣ)) : R))
          * steinbergX hij (s : R))
        * steinbergX hij (-((s : R) * (s : R))) := by
          rw [steinbergWeyl, steinbergWeyl]
          group
    _ = (steinbergX hij (-((r : R) * (r : R))) * steinbergX hij (r : R))
        * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
        * (steinbergX hij (r : R) * steinbergX hij (-1 : R) * steinbergX hij (s : R))
        * steinbergX (Ne.symm hij) (-(((s⁻¹ : Rˣ)) : R))
        * (steinbergX hij (s : R) * steinbergX hij (-((s : R) * (s : R)))) := by group
    _ = steinbergX hij ((r : R) * (s : R))
        * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
        * steinbergX (Ne.symm hij) (-(((s⁻¹ : Rˣ)) : R))
        * steinbergX hij ((r : R) * (s : R)) := by rw [hfirst, hmiddle, hlast]; group
    _ = steinbergX hij ((r : R) * (s : R))
        * steinbergX (Ne.symm hij) (-((((r * s)⁻¹ : Rˣ)) : R))
        * steinbergX hij ((r : R) * (s : R)) := by
        have hcombine : steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
            * steinbergX (Ne.symm hij) (-(((s⁻¹ : Rˣ)) : R))
            = steinbergX (Ne.symm hij) (-((((r * s)⁻¹ : Rˣ)) : R)) := by
          rw [steinbergX_mul]
          congr 1
          rw [← hinv]
          ring
        calc steinbergX hij ((r : R) * (s : R))
              * steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
              * steinbergX (Ne.symm hij) (-(((s⁻¹ : Rˣ)) : R))
              * steinbergX hij ((r : R) * (s : R))
            = steinbergX hij ((r : R) * (s : R))
              * (steinbergX (Ne.symm hij) (-(((r⁻¹ : Rˣ)) : R))
                * steinbergX (Ne.symm hij) (-(((s⁻¹ : Rˣ)) : R)))
              * steinbergX hij ((r : R) * (s : R)) := by group
          _ = steinbergX hij ((r : R) * (s : R))
              * steinbergX (Ne.symm hij) (-((((r * s)⁻¹ : Rˣ)) : R))
              * steinbergX hij ((r : R) * (s : R)) := by rw [hcombine]
    _ = steinbergWeyl hij (r * s) := by rfl

omit [DecidableEq n] [Fintype n] in
/-- Complementary units multiply exactly in the torus lift. -/
theorem steinbergTorus_product_of_add_one {i j k : n} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (r s : Rˣ) (hsum : (r : R) + (s : R) = 1) :
    steinbergTorus hij r * steinbergTorus hij s = steinbergTorus hij (r * s) := by
  rw [steinbergTorus]
  calc steinbergWeyl hij r * steinbergWeyl hij (-1 : Rˣ)
        * (steinbergWeyl hij s * steinbergWeyl hij (-1 : Rˣ))
      = (steinbergWeyl hij r * steinbergWeyl hij (-1 : Rˣ) * steinbergWeyl hij s)
        * steinbergWeyl hij (-1 : Rˣ) := by group
    _ = steinbergWeyl hij (r * s) * steinbergWeyl hij (-1 : Rˣ) := by
      rw [steinbergWeyl_product_of_add_one hij hik hjk r s hsum]

omit [DecidableEq n] [Fintype n] in
/-- **The Steinberg relation.**  Complementary units have trivial Steinberg symbol. -/
theorem steinbergSymbol_of_add_one {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (r s : Rˣ) (hsum : (r : R) + (s : R) = 1) :
    steinbergSymbol hij r s = 1 := by
  have htorus := steinbergTorus_product_of_add_one hij hik hjk r s hsum
  have htorus_swap := steinbergTorus_product_of_add_one hij hik hjk s r (by rw [add_comm, hsum])
  have hcomm : steinbergTorus hij r * steinbergTorus hij s
      = steinbergTorus hij s * steinbergTorus hij r := by
    calc steinbergTorus hij r * steinbergTorus hij s = steinbergTorus hij (r * s) := htorus
      _ = steinbergTorus hij (s * r) := by rw [mul_comm]
      _ = steinbergTorus hij s * steinbergTorus hij r := htorus_swap.symm
  rw [steinbergSymbol]
  calc steinbergTorus hij (r * s) * (steinbergTorus hij r)⁻¹ * (steinbergTorus hij s)⁻¹
      = (steinbergTorus hij r * steinbergTorus hij s)
        * (steinbergTorus hij r)⁻¹ * (steinbergTorus hij s)⁻¹ := by rw [htorus]
    _ = 1 := by rw [hcomm]; group

end GaloisForLFunctions.HTGeometry
