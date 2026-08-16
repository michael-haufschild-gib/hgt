import GaloisForLFunctions.HTGeometry.SteinbergTorusCommutator

/-!
# How the Weyl element acts on the generators

The Weyl element `w_ij(u) = x_ij(u) x_ji(−u⁻¹) x_ij(u)` conjugates the generators involving a third
index by swapping `i` and `j` and inserting `u⁻¹`:

```text
w_ij(u) x_ik(a) w_ij(u)⁻¹ = x_jk(−u⁻¹ a) ,
w_ij(u) x_kj(a) w_ij(u)⁻¹ = x_ki(a u⁻¹) .
```

Both are derived from the three Steinberg relations alone — the map to matrices is not injective, so
the matrix computation would not suffice.  Each is three conjugations: the outer `x_ij(u)` commutes
with the generator, the middle `x_ji(−u⁻¹)` produces a chained commutator, and the second `x_ij(u)`
produces another which cancels against the first factor.

Composing them along `x_ij(a) = [x_ik(a), x_kj(1)]` gives the classical formula

```text
w_ij(u) x_ij(a) w_ij(u)⁻¹ = x_ji(−u⁻¹ a u⁻¹) ,
```

which is the computation the Steinberg relation `{u, 1−u} = 1` runs on.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]

/-! ## The two forms of the chained relation -/

omit [DecidableEq n] in
/-- Conjugating the second factor of a chain by the first. -/
theorem steinbergX_conj_chain {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    steinbergX hij a * steinbergX hjk b * (steinbergX hij a)⁻¹
      = steinbergX hik (a * b) * steinbergX hjk b :=
  mul_inv_eq_iff_eq_mul.1 (steinbergX_chain hij hjk hik a b)

omit [DecidableEq n] in
/-- Conjugating the first factor of a chain by the second. -/
theorem steinbergX_conj_chain' {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    steinbergX hjk b * steinbergX hij a * (steinbergX hjk b)⁻¹
      = (steinbergX hik (a * b))⁻¹ * steinbergX hij a := by
  have h := steinbergX_chain hij hjk hik a b
  have h1 : steinbergX hjk b * (steinbergX hij a)⁻¹ * (steinbergX hjk b)⁻¹
      = (steinbergX hij a)⁻¹ * steinbergX hik (a * b) := by
    rw [← h]
    group
  have h2 := congrArg (fun z => z⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h2
  calc steinbergX hjk b * steinbergX hij a * (steinbergX hjk b)⁻¹
      = ((steinbergX hjk b) * (steinbergX hij a)⁻¹ * (steinbergX hjk b)⁻¹)⁻¹ := by group
    _ = ((steinbergX hij a)⁻¹ * steinbergX hik (a * b))⁻¹ := by rw [h1]
    _ = (steinbergX hik (a * b))⁻¹ * steinbergX hij a := by group

/-! ## The Weyl action on a generator with a third index -/

omit [DecidableEq n] in
/-- **The Weyl element moves the first index.** -/
theorem steinbergWeyl_conj_first {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (a : R) :
    steinbergWeyl hij u * steinbergX hik a * (steinbergWeyl hij u)⁻¹
      = steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a) := by
  have hji : j ≠ i := Ne.symm hij
  -- the outer generator commutes with `x_ik`
  have hcomm : steinbergX hij ((u : Rˣ) : R) * steinbergX hik a
      = steinbergX hik a * steinbergX hij ((u : Rˣ) : R) :=
    steinbergX_commute hij hik hji hik _ _
  have hstep1 : steinbergX hij ((u : Rˣ) : R) * steinbergX hik a
        * (steinbergX hij ((u : Rˣ) : R))⁻¹ = steinbergX hik a := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- the middle generator chains
  have hstep2 : steinbergX hji (-(((u⁻¹ : Rˣ) : R))) * steinbergX hik a
        * (steinbergX hji (-(((u⁻¹ : Rˣ) : R))))⁻¹
      = steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a) * steinbergX hik a :=
    steinbergX_conj_chain hji hik hjk _ _
  -- the outer generator chains against the new factor
  have hval : ((u : Rˣ) : R) * (-(((u⁻¹ : Rˣ) : R)) * a) = -a := by
    have hu : ((u : Rˣ) : R) * (((u⁻¹ : Rˣ)) : R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((u : Rˣ) : R) * (-(((u⁻¹ : Rˣ) : R)) * a)
        = -(((u : Rˣ) : R) * (((u⁻¹ : Rˣ)) : R)) * a := by ring
      _ = -a := by rw [hu]; ring
  have hstep3 : steinbergX hij ((u : Rˣ) : R) * steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a)
        * (steinbergX hij ((u : Rˣ) : R))⁻¹
      = steinbergX hik (-a) * steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a) := by
    have h := steinbergX_conj_chain hij hjk hik ((u : Rˣ) : R) (-(((u⁻¹ : Rˣ) : R)) * a)
    rwa [hval] at h
  -- the two `x_ik` factors cancel
  have hcomm2 : steinbergX hik (-a) * steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a)
      = steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a) * steinbergX hik (-a) :=
    steinbergX_commute hik hjk (Ne.symm hjk) hik _ _
  rw [steinbergWeyl]
  calc steinbergX hij ((u : Rˣ) : R) * steinbergX hji (-(((u⁻¹ : Rˣ) : R)))
        * steinbergX hij ((u : Rˣ) : R) * steinbergX hik a
        * (steinbergX hij ((u : Rˣ) : R) * steinbergX hji (-(((u⁻¹ : Rˣ) : R)))
          * steinbergX hij ((u : Rˣ) : R))⁻¹
      = steinbergX hij ((u : Rˣ) : R) * (steinbergX hji (-(((u⁻¹ : Rˣ) : R)))
          * (steinbergX hij ((u : Rˣ) : R) * steinbergX hik a
            * (steinbergX hij ((u : Rˣ) : R))⁻¹)
          * (steinbergX hji (-(((u⁻¹ : Rˣ) : R))))⁻¹)
          * (steinbergX hij ((u : Rˣ) : R))⁻¹ := by group
    _ = steinbergX hij ((u : Rˣ) : R) * (steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a)
          * steinbergX hik a) * (steinbergX hij ((u : Rˣ) : R))⁻¹ := by
        rw [hstep1, hstep2]
    _ = (steinbergX hij ((u : Rˣ) : R) * steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a)
          * (steinbergX hij ((u : Rˣ) : R))⁻¹)
        * (steinbergX hij ((u : Rˣ) : R) * steinbergX hik a
          * (steinbergX hij ((u : Rˣ) : R))⁻¹) := by group
    _ = (steinbergX hik (-a) * steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a))
        * steinbergX hik a := by rw [hstep1, hstep3]
    _ = steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a)
        * (steinbergX hik (-a) * steinbergX hik a) := by rw [hcomm2]; group
    _ = steinbergX hjk (-(((u⁻¹ : Rˣ) : R)) * a) := by
        rw [steinbergX_mul, neg_add_cancel, steinbergX_zero, mul_one]

omit [DecidableEq n] in
/-- **The Weyl element moves the second index.** -/
theorem steinbergWeyl_conj_second {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (b : R) :
    steinbergWeyl hij u * steinbergX (Ne.symm hjk) b * (steinbergWeyl hij u)⁻¹
      = steinbergX (Ne.symm hik) (b * (((u⁻¹ : Rˣ)) : R)) := by
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  set U : R := ((u : Rˣ) : R) with hU
  set V : R := (((u⁻¹ : Rˣ)) : R) with hV
  have huv : U * V = 1 := by
    rw [hU, hV, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- the outer generator commutes with `x_kj`
  have hstep1 : steinbergX hij U * steinbergX hkj b * (steinbergX hij U)⁻¹
      = steinbergX hkj b := by
    have hcomm : steinbergX hij U * steinbergX hkj b = steinbergX hkj b * steinbergX hij U :=
      steinbergX_commute hij hkj hjk hij _ _
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- the middle generator chains
  have hstep2 : steinbergX hji (-V) * steinbergX hkj b * (steinbergX hji (-V))⁻¹
      = steinbergX hki (b * V) * steinbergX hkj b := by
    have h := steinbergX_conj_chain' hkj hji hki b (-V)
    have hval : b * -V = -(b * V) := by ring
    rw [hval] at h
    have hinv : (steinbergX hki (-(b * V)))⁻¹ = steinbergX hki (b * V) := by
      rw [steinbergX_neg hki (b * V), inv_inv]
    rwa [hinv] at h
  -- the outer generator chains against the new factor
  have hstep3 : steinbergX hij U * steinbergX hki (b * V) * (steinbergX hij U)⁻¹
      = (steinbergX hkj b)⁻¹ * steinbergX hki (b * V) := by
    have h := steinbergX_conj_chain' hki hij hkj (b * V) U
    have hval : b * V * U = b := by
      calc b * V * U = b * (U * V) := by ring
        _ = b := by rw [huv, mul_one]
    rwa [hval] at h
  have hcomm2 : (steinbergX hkj b)⁻¹ * steinbergX hki (b * V)
      = steinbergX hki (b * V) * (steinbergX hkj b)⁻¹ := by
    have hc : steinbergX hki (b * V) * steinbergX hkj b
        = steinbergX hkj b * steinbergX hki (b * V) :=
      steinbergX_commute hki hkj hik hkj _ _
    exact (Commute.inv_left (Commute.symm hc)).eq
  rw [steinbergWeyl]
  calc steinbergX hij U * steinbergX hji (-V) * steinbergX hij U * steinbergX hkj b
        * (steinbergX hij U * steinbergX hji (-V) * steinbergX hij U)⁻¹
      = steinbergX hij U * (steinbergX hji (-V)
          * (steinbergX hij U * steinbergX hkj b * (steinbergX hij U)⁻¹)
          * (steinbergX hji (-V))⁻¹) * (steinbergX hij U)⁻¹ := by group
    _ = steinbergX hij U * (steinbergX hki (b * V) * steinbergX hkj b)
          * (steinbergX hij U)⁻¹ := by rw [hstep1, hstep2]
    _ = (steinbergX hij U * steinbergX hki (b * V) * (steinbergX hij U)⁻¹)
        * (steinbergX hij U * steinbergX hkj b * (steinbergX hij U)⁻¹) := by group
    _ = ((steinbergX hkj b)⁻¹ * steinbergX hki (b * V)) * steinbergX hkj b := by
        rw [hstep1, hstep3]
    _ = steinbergX hki (b * V) * ((steinbergX hkj b)⁻¹ * steinbergX hkj b) := by
        rw [hcomm2]; group
    _ = steinbergX hki (b * V) := by rw [inv_mul_cancel, mul_one]

omit [DecidableEq n] in
/-- **The classical Weyl conjugation formula.**  Composing the two moves along
`x_ij(a) = [x_ik(a), x_kj(1)]`. -/
theorem steinbergWeyl_conj_self {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (a : R) :
    steinbergWeyl hij u * steinbergX hij a * (steinbergWeyl hij u)⁻¹
      = steinbergX (Ne.symm hij) (-(((u⁻¹ : Rˣ) : R)) * a * (((u⁻¹ : Rˣ)) : R)) := by
  have hkj : k ≠ j := Ne.symm hjk
  have hji : j ≠ i := Ne.symm hij
  have hki : k ≠ i := Ne.symm hik
  set V : R := (((u⁻¹ : Rˣ)) : R) with hV
  have hcomm := steinbergX_eq_commutator hik hkj hij a
  have h1 := steinbergWeyl_conj_first hij hik hjk u a
  have h2 := steinbergWeyl_conj_second hij hik hjk u (1 : R)
  rw [one_mul] at h2
  have hchain := steinbergX_chain hjk hki hji (-V * a) V
  rw [hcomm]
  calc steinbergWeyl hij u * (steinbergX hik a * steinbergX hkj 1
        * (steinbergX hik a)⁻¹ * (steinbergX hkj 1)⁻¹) * (steinbergWeyl hij u)⁻¹
      = (steinbergWeyl hij u * steinbergX hik a * (steinbergWeyl hij u)⁻¹)
        * (steinbergWeyl hij u * steinbergX hkj 1 * (steinbergWeyl hij u)⁻¹)
        * (steinbergWeyl hij u * steinbergX hik a * (steinbergWeyl hij u)⁻¹)⁻¹
        * (steinbergWeyl hij u * steinbergX hkj 1 * (steinbergWeyl hij u)⁻¹)⁻¹ := by group
    _ = steinbergX hjk (-V * a) * steinbergX hki V * (steinbergX hjk (-V * a))⁻¹
        * (steinbergX hki V)⁻¹ := by rw [h1, h2]
    _ = steinbergX hji (-V * a * V) := hchain

omit [DecidableEq n] in
/-- **The Weyl element moves the first index of a row generator.**
`w_ij(u) x_jk(c) w_ij(u)⁻¹ = x_ik(u c)`. -/
theorem steinbergWeyl_conj_row {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (c : R) :
    steinbergWeyl hij u * steinbergX hjk c * (steinbergWeyl hij u)⁻¹
      = steinbergX hik ((((u : Rˣ)) : R) * c) := by
  have hji : j ≠ i := Ne.symm hij
  set U : R := ((u : Rˣ) : R) with hU
  set V : R := (((u⁻¹ : Rˣ)) : R) with hV
  have hvu : V * U = 1 := by
    rw [hU, hV, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- inner conjugation by `x_ij(U)`
  have hin : steinbergX hij U * steinbergX hjk c * (steinbergX hij U)⁻¹
      = steinbergX hik (U * c) * steinbergX hjk c :=
    steinbergX_conj_chain hij hjk hik U c
  -- the middle generator: it fixes `x_jk` and chains `x_ik`
  have hmid1 : steinbergX hji (-V) * steinbergX hik (U * c) * (steinbergX hji (-V))⁻¹
      = steinbergX hjk (-c) * steinbergX hik (U * c) := by
    have h := steinbergX_conj_chain hji hik hjk (-V) (U * c)
    have hval : -V * (U * c) = -c := by
      calc -V * (U * c) = -(V * U) * c := by ring
        _ = -c := by rw [hvu]; ring
    rwa [hval] at h
  have hmid2 : steinbergX hji (-V) * steinbergX hjk c * (steinbergX hji (-V))⁻¹
      = steinbergX hjk c := by
    have hcomm : steinbergX hji (-V) * steinbergX hjk c = steinbergX hjk c * steinbergX hji (-V) :=
      steinbergX_commute hji hjk hij hjk _ _
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- the outer generator
  have hout1 : steinbergX hij U * steinbergX hjk (-c) * (steinbergX hij U)⁻¹
      = steinbergX hik (U * -c) * steinbergX hjk (-c) :=
    steinbergX_conj_chain hij hjk hik U (-c)
  have hout2 : steinbergX hij U * steinbergX hik (U * c) * (steinbergX hij U)⁻¹
      = steinbergX hik (U * c) := by
    have hcomm : steinbergX hij U * steinbergX hik (U * c)
        = steinbergX hik (U * c) * steinbergX hij U :=
      steinbergX_commute hij hik hji hik _ _
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- the two families commute
  have hswap : ∀ a b : R, steinbergX hjk a * steinbergX hik b
      = steinbergX hik b * steinbergX hjk a := fun a b =>
    steinbergX_commute hjk hik (Ne.symm hik) hjk _ _
  have hcollect : steinbergX hik (U * -c) * steinbergX hjk (-c) * steinbergX hik (U * c)
        * (steinbergX hik (U * c) * steinbergX hjk c)
      = steinbergX hik (U * c) := by
    calc steinbergX hik (U * -c) * steinbergX hjk (-c) * steinbergX hik (U * c)
          * (steinbergX hik (U * c) * steinbergX hjk c)
        = steinbergX hik (U * -c) * (steinbergX hjk (-c) * steinbergX hik (U * c))
          * (steinbergX hik (U * c) * steinbergX hjk c) := by group
      _ = steinbergX hik (U * -c) * (steinbergX hik (U * c) * steinbergX hjk (-c))
          * (steinbergX hik (U * c) * steinbergX hjk c) := by rw [hswap]
      _ = steinbergX hik (U * -c) * steinbergX hik (U * c)
          * (steinbergX hjk (-c) * steinbergX hik (U * c)) * steinbergX hjk c := by group
      _ = steinbergX hik (U * -c) * steinbergX hik (U * c)
          * (steinbergX hik (U * c) * steinbergX hjk (-c)) * steinbergX hjk c := by rw [hswap]
      _ = (steinbergX hik (U * -c) * steinbergX hik (U * c) * steinbergX hik (U * c))
          * (steinbergX hjk (-c) * steinbergX hjk c) := by group
      _ = steinbergX hik (U * c) := by
          rw [steinbergX_mul, steinbergX_mul, steinbergX_mul, neg_add_cancel, steinbergX_zero,
            mul_one]
          congr 1
          ring
  rw [steinbergWeyl]
  calc steinbergX hij U * steinbergX hji (-V) * steinbergX hij U * steinbergX hjk c
        * (steinbergX hij U * steinbergX hji (-V) * steinbergX hij U)⁻¹
      = steinbergX hij U * (steinbergX hji (-V)
          * (steinbergX hij U * steinbergX hjk c * (steinbergX hij U)⁻¹)
          * (steinbergX hji (-V))⁻¹) * (steinbergX hij U)⁻¹ := by group
    _ = steinbergX hij U * ((steinbergX hji (-V) * steinbergX hik (U * c)
          * (steinbergX hji (-V))⁻¹)
        * (steinbergX hji (-V) * steinbergX hjk c * (steinbergX hji (-V))⁻¹))
        * (steinbergX hij U)⁻¹ := by rw [hin]; group
    _ = steinbergX hij U * ((steinbergX hjk (-c) * steinbergX hik (U * c))
          * steinbergX hjk c) * (steinbergX hij U)⁻¹ := by rw [hmid1, hmid2]
    _ = (steinbergX hij U * steinbergX hjk (-c) * (steinbergX hij U)⁻¹)
        * (steinbergX hij U * steinbergX hik (U * c) * (steinbergX hij U)⁻¹)
        * (steinbergX hij U * steinbergX hjk c * (steinbergX hij U)⁻¹) := by group
    _ = (steinbergX hik (U * -c) * steinbergX hjk (-c)) * steinbergX hik (U * c)
        * (steinbergX hik (U * c) * steinbergX hjk c) := by rw [hout1, hout2, hin]
    _ = steinbergX hik (U * c) := hcollect

omit [DecidableEq n] in
/-- **The Weyl element moves the second index of a column generator.**
`w_ij(u) x_ki(d) w_ij(u)⁻¹ = x_kj(−d u)`. -/
theorem steinbergWeyl_conj_col {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (d : R) :
    steinbergWeyl hij u * steinbergX (Ne.symm hik) d * (steinbergWeyl hij u)⁻¹
      = steinbergX (Ne.symm hjk) (-(d * (((u : Rˣ)) : R))) := by
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  set U : R := ((u : Rˣ) : R) with hU
  set V : R := (((u⁻¹ : Rˣ)) : R) with hV
  have huv : U * V = 1 := by
    rw [hU, hV, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  -- inner conjugation
  have hin : steinbergX hij U * steinbergX hki d * (steinbergX hij U)⁻¹
      = (steinbergX hkj (d * U))⁻¹ * steinbergX hki d :=
    steinbergX_conj_chain' hki hij hkj d U
  -- the middle generator sends the pair to a single factor
  have hmid1 : steinbergX hji (-V) * steinbergX hkj (d * U) * (steinbergX hji (-V))⁻¹
      = steinbergX hki d * steinbergX hkj (d * U) := by
    have h := steinbergX_conj_chain' hkj hji hki (d * U) (-V)
    have hval : d * U * -V = -d := by
      calc d * U * -V = -(d * (U * V)) := by ring
        _ = -d := by rw [huv, mul_one]
    rw [hval] at h
    have hinv : (steinbergX hki (-d))⁻¹ = steinbergX hki d := by
      rw [steinbergX_neg hki d, inv_inv]
    rwa [hinv] at h
  have hmid2 : steinbergX hji (-V) * steinbergX hki d * (steinbergX hji (-V))⁻¹
      = steinbergX hki d := by
    have hcomm : steinbergX hji (-V) * steinbergX hki d = steinbergX hki d * steinbergX hji (-V) :=
      steinbergX_commute hji hki hik hji _ _
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  -- the outer generator commutes with `x_kj`
  have hout : steinbergX hij U * steinbergX hkj (d * U) * (steinbergX hij U)⁻¹
      = steinbergX hkj (d * U) := by
    have hcomm : steinbergX hij U * steinbergX hkj (d * U)
        = steinbergX hkj (d * U) * steinbergX hij U :=
      steinbergX_commute hij hkj hjk hij _ _
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  rw [steinbergWeyl]
  calc steinbergX hij U * steinbergX hji (-V) * steinbergX hij U * steinbergX hki d
        * (steinbergX hij U * steinbergX hji (-V) * steinbergX hij U)⁻¹
      = steinbergX hij U * (steinbergX hji (-V)
          * (steinbergX hij U * steinbergX hki d * (steinbergX hij U)⁻¹)
          * (steinbergX hji (-V))⁻¹) * (steinbergX hij U)⁻¹ := by group
    _ = steinbergX hij U * ((steinbergX hji (-V) * steinbergX hkj (d * U)
          * (steinbergX hji (-V))⁻¹)⁻¹
        * (steinbergX hji (-V) * steinbergX hki d * (steinbergX hji (-V))⁻¹))
        * (steinbergX hij U)⁻¹ := by rw [hin]; group
    _ = steinbergX hij U * ((steinbergX hki d * steinbergX hkj (d * U))⁻¹
        * steinbergX hki d) * (steinbergX hij U)⁻¹ := by rw [hmid1, hmid2]
    _ = steinbergX hij U * (steinbergX hkj (d * U))⁻¹ * (steinbergX hij U)⁻¹ := by group
    _ = (steinbergX hij U * steinbergX hkj (d * U) * (steinbergX hij U)⁻¹)⁻¹ := by group
    _ = (steinbergX hkj (d * U))⁻¹ := by rw [hout]
    _ = steinbergX hkj (-(d * U)) := (steinbergX_neg hkj (d * U)).symm

omit [DecidableEq n] in
/-- **The Weyl element on the transposed generator.**  Composing the two row/column moves along
`x_ji(b) = [x_jk(b), x_ki(1)]`. -/
theorem steinbergWeyl_conj_transpose {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u : Rˣ) (b : R) :
    steinbergWeyl hij u * steinbergX (Ne.symm hij) b * (steinbergWeyl hij u)⁻¹
      = steinbergX hij (-(((u : Rˣ) : R) * b * (((u : Rˣ)) : R))) := by
  have hji : j ≠ i := Ne.symm hij
  have hkj : k ≠ j := Ne.symm hjk
  have hki : k ≠ i := Ne.symm hik
  set U : R := ((u : Rˣ) : R) with hU
  have hcomm := steinbergX_eq_commutator hjk hki hji b
  have h1 := steinbergWeyl_conj_row hij hik hjk u b
  have h2 := steinbergWeyl_conj_col hij hik hjk u (1 : R)
  rw [one_mul] at h2
  have hchain := steinbergX_chain hik hkj hij (U * b) (-U)
  have hval : U * b * -U = -(U * b * U) := by ring
  rw [hval] at hchain
  rw [hcomm]
  calc steinbergWeyl hij u * (steinbergX hjk b * steinbergX hki 1
        * (steinbergX hjk b)⁻¹ * (steinbergX hki 1)⁻¹) * (steinbergWeyl hij u)⁻¹
      = (steinbergWeyl hij u * steinbergX hjk b * (steinbergWeyl hij u)⁻¹)
        * (steinbergWeyl hij u * steinbergX hki 1 * (steinbergWeyl hij u)⁻¹)
        * (steinbergWeyl hij u * steinbergX hjk b * (steinbergWeyl hij u)⁻¹)⁻¹
        * (steinbergWeyl hij u * steinbergX hki 1 * (steinbergWeyl hij u)⁻¹)⁻¹ := by group
    _ = steinbergX hik (U * b) * steinbergX hkj (-U) * (steinbergX hik (U * b))⁻¹
        * (steinbergX hkj (-U))⁻¹ := by rw [h1, h2]
    _ = steinbergX hij (-(U * b * U)) := hchain

end GaloisForLFunctions.HTGeometry

end
