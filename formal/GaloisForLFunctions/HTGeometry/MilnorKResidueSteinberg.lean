import GaloisForLFunctions.HTGeometry.MilnorKResidueStep

/-!
# The Steinberg relation for the residue step

The residue of Milnor `K`-theory has to kill the two relation families.  Multilinearity is
`resStepHom_mul`.  This file assembles the identities the Steinberg relation needs: multiplication
by a degree-one class is computed on symbols, so a composite of two such multiplications is
multiplication by a two-slot symbol, and it vanishes exactly when that symbol does.

The three vanishing inputs are the Steinberg relation of the residue field, the relation
`{-u}{u} = 0`, and `{-1} + {-1} = 0`; anticommutativity relates the two orders of `{-1}` and a unit.
Together with the trivial vanishing of the step at a unit of residue one and valuation zero, they
give the Steinberg relation whenever the valuation of `a` is nonnegative.

* `mulSymbol_class`, `mulSymbol_comp_class` : multiplication by degree-one classes on symbols.
* `mulSymbol_comp_steinberg`, `mulSymbol_comp_neg_self`, `mulSymbol_add_self_neg_one`,
  `mulSymbol_comp_neg_one_anticomm` : the vanishing and commutation inputs.
* `resStepHom_steinberg_of_nonneg` : **the Steinberg relation for the residue step when
  `0 ≤ v(a)`.**
-/

namespace GaloisForLFunctions.HTGeometry

section SteinbergInputs

variable {k : Type*} [Field k]

theorem mulSymbol_class (u : kˣ) (n : ℕ) (s : MilnorSymbolDeg k n) :
    mulSymbol u n (milnorClassDeg k n s)
      = milnorClassDeg k (n + 1) ⟨u :: s.val, by rw [List.length_cons, s.property]⟩ := by
  show milnorDegCongr (Nat.add_comm 1 n)
      (milnorMul k 1 n (resSymbol u) (milnorClassDeg k n s)) = _
  rw [resSymbol, milnorMul_class]
  exact milnorDegCongr_class _ _ _ rfl

theorem mulSymbol_comp_class (u v : kˣ) (n : ℕ) (s : MilnorSymbolDeg k n) :
    mulSymbol u (n + 1) (mulSymbol v n (milnorClassDeg k n s))
      = milnorClassDeg k (n + 2)
          ⟨u :: v :: s.val, by rw [List.length_cons, List.length_cons, s.property]⟩ := by
  rw [mulSymbol_class, mulSymbol_class]

/-- **Multiplication by `1` is zero.** -/
theorem mulSymbol_one_eq_zero (n : ℕ) : mulSymbol (1 : kˣ) n = 0 := by
  show (milnorDegCongr (Nat.add_comm 1 n)).comp (milnorMul k 1 n (resSymbol (1 : kˣ))) = 0
  rw [resSymbol_one, map_zero]
  exact AddMonoidHom.comp_zero _

/-- **`{-1} + {-1} = 0`**, as an operator. -/
theorem mulSymbol_add_self_neg_one (n : ℕ) :
    mulSymbol (-1 : kˣ) n + mulSymbol (-1 : kˣ) n = 0 := by
  rw [← mulSymbol_mul, show (-1 : kˣ) * (-1 : kˣ) = 1 by simp, mulSymbol_one_eq_zero]

theorem mulSymbol_neg_one_add_self_apply (n : ℕ) (z : MilnorKDeg k n) :
    mulSymbol (-1 : kˣ) n z + mulSymbol (-1 : kˣ) n z = 0 := by
  have h := mulSymbol_add_self_neg_one (k := k) n
  exact congrArg (fun f : MilnorKDeg k n →+ MilnorKDeg k (n + 1) => f z) h

/-- Any even multiple of the image of a class divisible by `{-1}` vanishes. -/
theorem zsmul_map_mulSymbol_neg_one_eq_zero {A : Type*} [AddCommGroup A] (n : ℕ) (c : ℤ)
    (f : MilnorKDeg k (n + 1) →+ A) (z : MilnorKDeg k n) :
    ((c + c) • f (mulSymbol (-1 : kˣ) n z)) = 0 := by
  rw [add_zsmul, ← smul_add, ← map_add, mulSymbol_neg_one_add_self_apply, map_zero, smul_zero]

/-- For any integer `α` and any sign `t`, the integer `α² - tα` is even. -/
theorem exists_add_self_sq_sub_sign (α : ℤ) {t : ℤ} (ht : t = 1 ∨ t = -1) :
    ∃ d : ℤ, α * α - t * α = d + d := by
  rcases ht with rfl | rfl
  · obtain ⟨d, hd⟩ := Int.even_mul_succ_self (α - 1)
    exact ⟨d, by rw [← hd]; ring⟩
  · obtain ⟨d, hd⟩ := Int.even_mul_succ_self α
    exact ⟨d, by rw [← hd]; ring⟩

theorem neg_one_pow_eq_one_or (m : ℕ) : ((-1 : ℤ) ^ m = 1) ∨ ((-1 : ℤ) ^ m = -1) := by
  rcases Nat.even_or_odd m with he | ho
  · exact Or.inl he.neg_one_pow
  · exact Or.inr ho.neg_one_pow

/-- Any even multiple of a class divisible by `{-1}` vanishes. -/
theorem zsmul_mulSymbol_neg_one_eq_zero (n : ℕ) (c : ℤ) (z : MilnorKDeg k n) :
    ((c + c) • mulSymbol (-1 : kˣ) n z) = 0 := by
  rw [add_zsmul, ← smul_add, mulSymbol_neg_one_add_self_apply, smul_zero]

/-- **The Steinberg relation as an operator**: multiplying by `{a}` and then by `{1 - a}` is
zero. -/
theorem mulSymbol_comp_steinberg {u : kˣ} (hu : (u : k) ≠ 1) (n : ℕ) :
    (mulSymbol u (n + 1)).comp (mulSymbol (oneSubUnit hu) n) = 0 := by
  refine milnorKDeg_hom_ext k fun s => ?_
  obtain ⟨l, rfl⟩ := s
  show mulSymbol u (l.length + 1)
      (mulSymbol (oneSubUnit hu) l.length (milnorClassDeg k l.length ⟨l, rfl⟩)) = 0
  rw [mulSymbol_comp_class]
  exact milnorClassDeg_steinberg_of_eq k hu [] l rfl _

/-- **`{-u}{u} = 0` as an operator.** -/
theorem mulSymbol_comp_neg_self (u : kˣ) (n : ℕ) :
    (mulSymbol (-u) (n + 1)).comp (mulSymbol u n) = 0 := by
  refine milnorKDeg_hom_ext k fun s => ?_
  obtain ⟨l, rfl⟩ := s
  show mulSymbol (-u) (l.length + 1) (mulSymbol u l.length (milnorClassDeg k l.length ⟨l, rfl⟩)) = 0
  rw [mulSymbol_comp_class]
  have h := milnorPairClass_neg_self (F := k) [] l (-u)
  rw [neg_neg] at h
  exact h

/-- **Anticommutativity as an operator.** -/
theorem mulSymbol_comp_neg_one_anticomm (u : kˣ) (n : ℕ) :
    (mulSymbol (-1 : kˣ) (n + 1)).comp (mulSymbol u n)
      = -((mulSymbol u (n + 1)).comp (mulSymbol (-1 : kˣ) n)) := by
  refine milnorKDeg_hom_ext k fun s => ?_
  obtain ⟨l, rfl⟩ := s
  show mulSymbol (-1 : kˣ) (l.length + 1)
      (mulSymbol u l.length (milnorClassDeg k l.length ⟨l, rfl⟩)) = _
  show _ = -(mulSymbol u (l.length + 1)
      (mulSymbol (-1 : kˣ) l.length (milnorClassDeg k l.length ⟨l, rfl⟩)))
  rw [mulSymbol_comp_class, mulSymbol_comp_class]
  exact milnorPairClass_anticomm [] l (-1 : kˣ) u

end SteinbergInputs

section StepVanishing

variable {K : Type*} [Field K] {k : Type*} [Field k] (D : ResidueData K k)

/-- **The step at a unit of residue one and valuation zero is zero.** -/
theorem resStepHom_eq_zero (b : Kˣ) (n : ℕ) (h1 : D.residueUnit b = 1) (h2 : D.val' b = 0) :
    resStepHom D b n = 0 := by
  cases n with
  | zero =>
      refine AddMonoidHom.ext fun p => ?_
      rw [resStepHom_zero_apply, h1, h2]
      refine Prod.ext ?_ ?_
      · show mulSymbol (1 : kˣ) 0 p.1 = 0
        rw [mulSymbol_one_eq_zero]
        rfl
      · show (0 : ℤ) • p.1 = 0
        rw [zero_zsmul]
  | succ m =>
      refine AddMonoidHom.ext fun p => ?_
      rw [resStepHom_succ_apply, h1, h2]
      refine Prod.ext ?_ ?_
      · show mulSymbol (1 : kˣ) (m + 1) p.1 = 0
        rw [mulSymbol_one_eq_zero]
        rfl
      · show mulSymbol (1 : kˣ) m p.2 + ((-1 : ℤ) ^ (m + 1) * 0) • p.1
            + ((-1 : ℤ) ^ m * 0) • mulSymbol (-1 : kˣ) m p.2 = 0
        rw [mulSymbol_one_eq_zero]
        simp

theorem resStepHom_zero_apply_of_val_zero (b : Kˣ) (h : D.val' b = 0)
    (p : MilnorKDeg k 0 × MilnorKDeg k 0) :
    resStepHom D b 0 p = (mulSymbol (D.residueUnit b) 0 p.1, 0) := by
  rw [resStepHom_zero_apply, h, zero_zsmul]

theorem resStepHom_succ_apply_of_val_zero (b : Kˣ) (m : ℕ) (h : D.val' b = 0)
    (p : MilnorKDeg k (m + 1) × MilnorKDeg k m) :
    resStepHom D b (m + 1) p
      = (mulSymbol (D.residueUnit b) (m + 1) p.1, mulSymbol (D.residueUnit b) m p.2) := by
  rw [resStepHom_succ_apply, h]
  simp

/-- **The Steinberg relation for the residue step at a unit of nonnegative valuation.**  Either
`1 - a` has valuation zero and residue one, or `a` does, or both do — and in the last case the
residue field's own Steinberg relation applies. -/
theorem resStepHom_steinberg_of_nonneg {a : Kˣ} (ha : (a : K) ≠ 1) (hnn : 0 ≤ D.val' a) (n : ℕ) :
    (resStepHom D a (n + 1)).comp (resStepHom D (oneSubUnit ha) n) = 0 := by
  rcases lt_or_eq_of_le hnn with hpos | hzero
  · -- `v a > 0`: then `1 - a` has valuation zero and residue one, so the inner step is zero.
    obtain ⟨hmem, hres⟩ := D.oneSub_of_pos ha hpos
    have hval : D.val' (oneSubUnit ha) = 0 := D.toTameData.mem_ker_iff.1 hmem
    have hru : D.residueUnit (oneSubUnit ha) = 1 := by
      rw [D.residueUnit_of_mem_ker hmem]
      exact hres
    rw [resStepHom_eq_zero D (oneSubUnit ha) n hru hval]
    exact AddMonoidHom.comp_zero _
  · -- `v a = 0`.
    have hmemA : a ∈ D.val.ker := D.toTameData.mem_ker_iff.2 hzero.symm
    obtain ⟨hle, himp⟩ := D.oneSub_of_zero ha hmemA
    rcases lt_or_eq_of_le hle with hbpos | hbzero
    · -- `v (1 - a) > 0`: then `a` has residue one, so the outer step is zero.
      have hru : D.residueUnit a = 1 := by
        rw [D.residueUnit_of_mem_ker hmemA]
        exact himp hbpos
      rw [resStepHom_eq_zero D a (n + 1) hru hzero.symm]
      exact AddMonoidHom.zero_comp _
    · -- both have valuation zero: the residue field's Steinberg relation applies.
      have hmemB : oneSubUnit ha ∈ D.val.ker := D.toTameData.mem_ker_iff.2 hbzero.symm
      have hvalB : D.val' (oneSubUnit ha) = 0 := hbzero.symm
      have hresB : ((D.residueUnit (oneSubUnit ha) : kˣ) : k)
          = 1 - ((D.residueUnit a : kˣ) : k) := by
        rw [D.residueUnit_of_mem_ker hmemB, D.residueUnit_of_mem_ker hmemA]
        exact D.oneSub_res ha hmemA hmemB
      have hane : ((D.residueUnit a : kˣ) : k) ≠ 1 := by
        intro hone
        refine (D.residueUnit (oneSubUnit ha)).ne_zero ?_
        rw [hresB, hone, sub_self]
      have hbeq : D.residueUnit (oneSubUnit ha) = oneSubUnit hane := by
        refine Units.ext ?_
        rw [hresB, oneSubUnit_val]
      cases n with
      | zero =>
          refine AddMonoidHom.ext fun p => ?_
          show resStepHom D a 1 (resStepHom D (oneSubUnit ha) 0
              ((p.1, p.2) : MilnorKDeg k 0 × MilnorKDeg k 0)) = 0
          rw [resStepHom_zero_apply_of_val_zero D (oneSubUnit ha) hvalB,
            resStepHom_succ_apply_of_val_zero D a 0 hzero.symm, hbeq]
          refine Prod.ext ?_ ?_
          · exact congrArg (fun f : MilnorKDeg k 0 →+ MilnorKDeg k 2 => f p.1)
              (mulSymbol_comp_steinberg hane 0)
          · exact map_zero _
      | succ m =>
          refine AddMonoidHom.ext fun p => ?_
          show resStepHom D a (m + 1 + 1) (resStepHom D (oneSubUnit ha) (m + 1)
              ((p.1, p.2) : MilnorKDeg k (m + 1) × MilnorKDeg k m)) = 0
          rw [resStepHom_succ_apply_of_val_zero D (oneSubUnit ha) m hvalB,
            resStepHom_succ_apply_of_val_zero D a (m + 1) hzero.symm, hbeq]
          refine Prod.ext ?_ ?_
          · exact congrArg (fun f : MilnorKDeg k (m + 1) →+ MilnorKDeg k (m + 3) => f p.1)
              (mulSymbol_comp_steinberg hane (m + 1))
          · exact congrArg (fun f : MilnorKDeg k m →+ MilnorKDeg k (m + 2) => f p.2)
              (mulSymbol_comp_steinberg hane m)

/-- The residues of `a` and `1 - a` are negatives of each other when `v a < 0`. -/
theorem residueUnit_eq_neg_of_neg {a : Kˣ} (ha : (a : K) ≠ 1) (hneg : D.val' a < 0) :
    D.residueUnit a = -(D.residueUnit (oneSubUnit ha)) := by
  obtain ⟨_, hmem, hres⟩ := D.oneSub_of_neg ha hneg
  have h1 : D.residueUnit (a * (oneSubUnit ha)⁻¹ * oneSubUnit ha)
      = D.residueUnit (a * (oneSubUnit ha)⁻¹) * D.residueUnit (oneSubUnit ha) :=
    D.residueUnit_mul _ _
  rw [inv_mul_cancel_right] at h1
  rw [h1, D.residueUnit_of_mem_ker hmem, hres, neg_one_mul]

/-- **The Steinberg relation for the residue step at a unit of negative valuation, in degree
zero.**  Here `1 - a` has the same valuation as `a` and the two residues are negatives of each
other, so `{ā}{b̄} = 0`; what is left is an even multiple of a class divisible by `{-1}`, and
`{-1} + {-1} = 0`. -/
theorem resStepHom_steinberg_of_neg_zero {a : Kˣ} (ha : (a : K) ≠ 1) (hneg : D.val' a < 0) :
    (resStepHom D a 1).comp (resStepHom D (oneSubUnit ha) 0) = 0 := by
  obtain ⟨hbval, -⟩ := D.oneSub_of_neg ha hneg
  have hares : D.residueUnit a = -(D.residueUnit (oneSubUnit ha)) :=
    residueUnit_eq_neg_of_neg D ha hneg
  have hbeta : D.val' (oneSubUnit ha) = D.val' a := hbval
  have hA : mulSymbol (D.residueUnit a) 0
      = mulSymbol (-1 : kˣ) 0 + mulSymbol (D.residueUnit (oneSubUnit ha)) 0 := by
    rw [hares, show -(D.residueUnit (oneSubUnit ha)) = (-1 : kˣ) * D.residueUnit (oneSubUnit ha) by
      rw [neg_one_mul], mulSymbol_mul]
  have hAB : (mulSymbol (D.residueUnit a) 1).comp
      (mulSymbol (D.residueUnit (oneSubUnit ha)) 0) = 0 := by
    rw [hares]
    exact mulSymbol_comp_neg_self _ 0
  refine AddMonoidHom.ext fun p => ?_
  show resStepHom D a 1 (resStepHom D (oneSubUnit ha) 0
      ((p.1, p.2) : MilnorKDeg k 0 × MilnorKDeg k 0)) = 0
  rw [resStepHom_zero_apply, resStepHom_succ_apply, hbeta]
  refine Prod.ext ?_ ?_
  · exact congrArg (fun f : MilnorKDeg k 0 →+ MilnorKDeg k 2 => f p.1) hAB
  · show mulSymbol (D.residueUnit a) 0 (D.val' a • p.1)
        + ((-1 : ℤ) ^ 1 * D.val' a) • mulSymbol (D.residueUnit (oneSubUnit ha)) 0 p.1
        + ((-1 : ℤ) ^ 0 * D.val' a) • mulSymbol (-1 : kˣ) 0 (D.val' a • p.1) = 0
    obtain ⟨d, hd⟩ := Int.even_mul_succ_self (D.val' a)
    have hkey : mulSymbol (D.residueUnit a) 0 (D.val' a • p.1)
        + ((-1 : ℤ) ^ 1 * D.val' a) • mulSymbol (D.residueUnit (oneSubUnit ha)) 0 p.1
        + ((-1 : ℤ) ^ 0 * D.val' a) • mulSymbol (-1 : kˣ) 0 (D.val' a • p.1)
        = (d + d) • mulSymbol (-1 : kˣ) 0 p.1 := by
      rw [hA]
      simp only [AddMonoidHom.add_apply, map_zsmul, pow_one, pow_zero, one_mul, neg_one_mul,
        neg_zsmul, ← mul_zsmul]
      rw [show D.val' a * D.val' a = d + d - D.val' a by rw [← hd]; ring]
      rw [sub_zsmul, add_zsmul]
      simp only [smul_add]
      abel
    rw [hkey]
    exact zsmul_mulSymbol_neg_one_eq_zero 0 d p.1

/-- **The Steinberg relation for the residue step at a unit of negative valuation, in positive
degree.** -/
theorem resStepHom_steinberg_of_neg_succ {a : Kˣ} (ha : (a : K) ≠ 1) (hneg : D.val' a < 0)
    (m : ℕ) :
    (resStepHom D a (m + 1 + 1)).comp (resStepHom D (oneSubUnit ha) (m + 1)) = 0 := by
  obtain ⟨hbval, -⟩ := D.oneSub_of_neg ha hneg
  have hares : D.residueUnit a = -(D.residueUnit (oneSubUnit ha)) :=
    residueUnit_eq_neg_of_neg D ha hneg
  have hbeta : D.val' (oneSubUnit ha) = D.val' a := hbval
  have hA : ∀ j : ℕ, mulSymbol (D.residueUnit a) j
      = mulSymbol (-1 : kˣ) j + mulSymbol (D.residueUnit (oneSubUnit ha)) j := by
    intro j
    rw [hares, show -(D.residueUnit (oneSubUnit ha)) = (-1 : kˣ) * D.residueUnit (oneSubUnit ha) by
      rw [neg_one_mul], mulSymbol_mul]
  have hAB : ∀ j : ℕ, (mulSymbol (D.residueUnit a) (j + 1)).comp
      (mulSymbol (D.residueUnit (oneSubUnit ha)) j) = 0 := by
    intro j
    rw [hares]
    exact mulSymbol_comp_neg_self _ j
  have hBB : ∀ (j : ℕ) (z : MilnorKDeg k j),
      mulSymbol (D.residueUnit (oneSubUnit ha)) (j + 1)
          (mulSymbol (D.residueUnit (oneSubUnit ha)) j z)
        = -(mulSymbol (-1 : kˣ) (j + 1)
            (mulSymbol (D.residueUnit (oneSubUnit ha)) j z)) := by
    intro j z
    have h0 : mulSymbol (D.residueUnit a) (j + 1)
        (mulSymbol (D.residueUnit (oneSubUnit ha)) j z) = 0 :=
      congrArg (fun f : MilnorKDeg k j →+ MilnorKDeg k (j + 2) => f z) (hAB j)
    rw [hA (j + 1), AddMonoidHom.add_apply] at h0
    exact (neg_eq_of_add_eq_zero_right h0).symm
  have hanti : ∀ (j : ℕ) (z : MilnorKDeg k j),
      mulSymbol (-1 : kˣ) (j + 1) (mulSymbol (D.residueUnit (oneSubUnit ha)) j z)
        = -(mulSymbol (D.residueUnit (oneSubUnit ha)) (j + 1) (mulSymbol (-1 : kˣ) j z)) :=
    fun j z => congrArg (fun f : MilnorKDeg k j →+ MilnorKDeg k (j + 2) => f z)
      (mulSymbol_comp_neg_one_anticomm (D.residueUnit (oneSubUnit ha)) j)
  obtain ⟨d, hd⟩ := exists_add_self_sq_sub_sign (D.val' a) (neg_one_pow_eq_one_or m)
  have ht2 : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
    rcases neg_one_pow_eq_one_or m with h | h <;> rw [h] <;> ring
  have hp1 : ((-1 : ℤ)) ^ (m + 1) = -((-1 : ℤ) ^ m) := by rw [pow_succ]; ring
  have hp2 : ((-1 : ℤ)) ^ (m + 1 + 1) = (-1 : ℤ) ^ m := by rw [pow_succ, pow_succ]; ring
  have hc : ((-1 : ℤ) ^ m * D.val' a) * ((-1 : ℤ) ^ m * D.val' a)
      = (d + d) + ((-1 : ℤ) ^ m * D.val' a) := by
    rw [show ((-1 : ℤ) ^ m * D.val' a) * ((-1 : ℤ) ^ m * D.val' a)
        = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ m) * (D.val' a * D.val' a) by ring, ht2, one_mul, ← hd]
    ring
  refine AddMonoidHom.ext fun p => ?_
  show resStepHom D a (m + 1 + 1) (resStepHom D (oneSubUnit ha) (m + 1)
      ((p.1, p.2) : MilnorKDeg k (m + 1) × MilnorKDeg k m)) = 0
  rw [resStepHom_succ_apply, resStepHom_succ_apply, hbeta]
  refine Prod.ext ?_ ?_
  · exact congrArg (fun f : MilnorKDeg k (m + 1) →+ MilnorKDeg k (m + 3) => f p.1) (hAB (m + 1))
  · have hexp : mulSymbol (D.residueUnit a) (m + 1)
            (mulSymbol (D.residueUnit (oneSubUnit ha)) m p.2
              + ((-1 : ℤ) ^ (m + 1) * D.val' a) • p.1
              + ((-1 : ℤ) ^ m * D.val' a) • mulSymbol (-1 : kˣ) m p.2)
          + ((-1 : ℤ) ^ (m + 1 + 1) * D.val' a)
              • mulSymbol (D.residueUnit (oneSubUnit ha)) (m + 1) p.1
          + ((-1 : ℤ) ^ (m + 1) * D.val' a) • mulSymbol (-1 : kˣ) (m + 1)
              (mulSymbol (D.residueUnit (oneSubUnit ha)) m p.2
                + ((-1 : ℤ) ^ (m + 1) * D.val' a) • p.1
                + ((-1 : ℤ) ^ m * D.val' a) • mulSymbol (-1 : kˣ) m p.2)
        = (((-1 : ℤ) ^ m * D.val' a) * ((-1 : ℤ) ^ m * D.val' a) - ((-1 : ℤ) ^ m * D.val' a))
              • mulSymbol (-1 : kˣ) (m + 1) p.1
          + (((-1 : ℤ) ^ m * D.val' a)
                - ((-1 : ℤ) ^ m * D.val' a) * ((-1 : ℤ) ^ m * D.val' a))
              • mulSymbol (-1 : kˣ) (m + 1) (mulSymbol (-1 : kˣ) m p.2)
          + (((-1 : ℤ) ^ m * D.val' a) + ((-1 : ℤ) ^ m * D.val' a))
              • mulSymbol (D.residueUnit (oneSubUnit ha)) (m + 1)
                  (mulSymbol (-1 : kˣ) m p.2) := by
      rw [hA (m + 1)]
      simp only [AddMonoidHom.add_apply, map_add, map_zsmul, hp1, hp2, hBB m p.2,
        hanti m p.2, neg_mul, smul_add, smul_smul]
      module
    rw [hexp,
      show ((-1 : ℤ) ^ m * D.val' a) * ((-1 : ℤ) ^ m * D.val' a) - ((-1 : ℤ) ^ m * D.val' a)
          = d + d from by rw [hc]; ring,
      show ((-1 : ℤ) ^ m * D.val' a)
            - ((-1 : ℤ) ^ m * D.val' a) * ((-1 : ℤ) ^ m * D.val' a) = (-d) + (-d) from by
        rw [hc]; ring,
      zsmul_mulSymbol_neg_one_eq_zero (m + 1) d p.1,
      zsmul_mulSymbol_neg_one_eq_zero (m + 1) (-d) (mulSymbol (-1 : kˣ) m p.2),
      zsmul_map_mulSymbol_neg_one_eq_zero m ((-1 : ℤ) ^ m * D.val' a)
        (mulSymbol (D.residueUnit (oneSubUnit ha)) (m + 1)) p.2]
    simp

/-- **The Steinberg relation for the residue step.**  Multiplying by `[ū_a] + v(a)ξ` and then by
`[ū_{1-a}] + v(1-a)ξ` is zero, whatever the valuation of `a`. -/
theorem resStepHom_steinberg {a : Kˣ} (ha : (a : K) ≠ 1) (n : ℕ) :
    (resStepHom D a (n + 1)).comp (resStepHom D (oneSubUnit ha) n) = 0 := by
  rcases le_or_gt 0 (D.val' a) with hnn | hneg
  · exact resStepHom_steinberg_of_nonneg D ha hnn n
  · cases n with
    | zero => exact resStepHom_steinberg_of_neg_zero D ha hneg
    | succ m => exact resStepHom_steinberg_of_neg_succ D ha hneg m

/-- **A Steinberg pair anywhere in the list makes the whole fold vanish.** -/
theorem resFold_eq_zero_of_steinberg (l₁ l₂ : List Kˣ) {a : Kˣ} (ha : (a : K) ≠ 1) (n : ℕ) :
    resFold D (l₁ ++ a :: oneSubUnit ha :: l₂) n = 0 := by
  induction l₁ with
  | nil =>
      refine AddMonoidHom.ext fun p => ?_
      show resStepHom D a (n + l₂.length + 1)
        (resStepHom D (oneSubUnit ha) (n + l₂.length) (resFold D l₂ n p)) = 0
      exact DFunLike.congr_fun (resStepHom_steinberg D ha (n + l₂.length)) (resFold D l₂ n p)
  | cons b t ih =>
      refine AddMonoidHom.ext fun p => ?_
      show resStepHom D b (n + (t ++ a :: oneSubUnit ha :: l₂).length)
        (resFold D (t ++ a :: oneSubUnit ha :: l₂) n p) = 0
      rw [show resFold D (t ++ a :: oneSubUnit ha :: l₂) n p = 0 from
        DFunLike.congr_fun ih p, map_zero]

end StepVanishing

end GaloisForLFunctions.HTGeometry
