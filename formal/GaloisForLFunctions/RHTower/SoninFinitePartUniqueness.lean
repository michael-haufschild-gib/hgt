import GaloisForLFunctions.RHTower.SoninPrincipalRelativeTraceSplitting

/-!
# The signed finite part is the only functional with the two normalizations

The operators presented as a finite prime principal shell plus an exact relative correction form a
subspace of the bounded operators.  Directness of the presentation makes the signed finite part
descend to a linear functional on that subspace, and it is the *unique* one whose value on a
principal shell is the logarithmic orbital trace and whose value on the relative ideal is the
ordinary trace: every element splits, so any linear functional with those two restrictions is
their sum.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap SoninPrincipalRelativePresentation

/-- The operators carrying a finite prime principal-relative presentation. -/
def soninPrincipalRelativeRange {n : ℕ} (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) :
    Submodule ℂ (evenSubspace →L[ℂ] evenSubspace) where
  carrier := Set.range (toOperator (a := a) (p := p) (hp := hp))
  add_mem' := by
    rintro _ _ ⟨X, rfl⟩ ⟨Y, rfl⟩
    exact ⟨X + Y, toOperator_add X Y⟩
  zero_mem' := ⟨0, toOperator_zero⟩
  smul_mem' := by
    rintro c _ ⟨X, rfl⟩
    exact ⟨c • X, toOperator_smul c X⟩

variable {n : ℕ} {a : ℝ} {p : Fin n → ℕ} {hp : ∀ i, (p i).Prime}

theorem toOperator_mem_soninPrincipalRelativeRange
    (X : SoninPrincipalRelativePresentation a p hp) :
    toOperator X ∈ soninPrincipalRelativeRange a p hp := ⟨X, rfl⟩

/-- A principal shell carries a presentation. -/
theorem shell_mem_soninPrincipalRelativeRange (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninPrincipalShellCombination a p hp A ∈ soninPrincipalRelativeRange a p hp :=
  ⟨⟨A, 0, IsSoninPrincipalRelativeIdeal.zero⟩, by simp [toOperator]⟩

/-- An exact relative correction carries a presentation. -/
theorem relative_mem_soninPrincipalRelativeRange (a : ℝ) (p : Fin n → ℕ)
    (hp : ∀ i, (p i).Prime) {K : evenSubspace →L[ℂ] evenSubspace}
    (hK : IsSoninPrincipalRelativeIdeal K) :
    K ∈ soninPrincipalRelativeRange a p hp :=
  ⟨⟨0, K, hK⟩, by simp [toOperator]⟩

/-- The signed finite part read off any presentation of the operator. -/
def soninFinitePartOfMem (T : soninPrincipalRelativeRange a p hp) : ℂ :=
  finitePart (Classical.choose T.2)

theorem soninFinitePartOfMem_eq (ha : 0 < a) (hinj : Function.Injective p)
    (T : soninPrincipalRelativeRange a p hp)
    (X : SoninPrincipalRelativePresentation a p hp)
    (hX : toOperator X = (T : evenSubspace →L[ℂ] evenSubspace)) :
    soninFinitePartOfMem T = finitePart X :=
  finitePart_eq_of_toOperator_eq ha hinj ((Classical.choose_spec T.2).trans hX.symm)

/-- **The signed finite part as a linear functional on the presented operators.** -/
def soninFinitePartₗ (ha : 0 < a) (hinj : Function.Injective p) :
    soninPrincipalRelativeRange a p hp →ₗ[ℂ] ℂ where
  toFun := soninFinitePartOfMem
  map_add' T S := by
    obtain ⟨X, hX⟩ := T.2
    obtain ⟨Y, hY⟩ := S.2
    rw [soninFinitePartOfMem_eq ha hinj T X hX, soninFinitePartOfMem_eq ha hinj S Y hY,
      soninFinitePartOfMem_eq ha hinj (T + S) (X + Y) (by
        rw [toOperator_add, hX, hY]; rfl), finitePart_add]
  map_smul' c T := by
    obtain ⟨X, hX⟩ := T.2
    rw [soninFinitePartOfMem_eq ha hinj T X hX,
      soninFinitePartOfMem_eq ha hinj (c • T) (c • X) (by
        rw [toOperator_smul, hX]; rfl), finitePart_smul]
    rfl

theorem soninFinitePartₗ_apply (ha : 0 < a) (hinj : Function.Injective p)
    (T : soninPrincipalRelativeRange a p hp) :
    soninFinitePartₗ ha hinj T = soninFinitePartOfMem T := rfl

@[simp] theorem soninFinitePartₗ_toOperator (ha : 0 < a) (hinj : Function.Injective p)
    (X : SoninPrincipalRelativePresentation a p hp) :
    soninFinitePartₗ ha hinj ⟨toOperator X, toOperator_mem_soninPrincipalRelativeRange X⟩ =
      finitePart X :=
  soninFinitePartOfMem_eq ha hinj _ X rfl

/-- On a principal shell the functional is the logarithmic orbital trace. -/
theorem soninFinitePartₗ_shell (ha : 0 < a) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    soninFinitePartₗ (hp := hp) ha hinj
        ⟨finitePrimeSoninPrincipalShellCombination a p hp A,
          shell_mem_soninPrincipalRelativeRange a p hp A⟩ =
      principalTrace p A := by
  rw [soninFinitePartₗ_apply,
    soninFinitePartOfMem_eq ha hinj _ ⟨A, 0, IsSoninPrincipalRelativeIdeal.zero⟩
    (by simp [toOperator])]
  simp [finitePart]

/-- On the relative ideal the functional is the ordinary trace. -/
theorem soninFinitePartₗ_relative (ha : 0 < a) (hinj : Function.Injective p)
    {K : evenSubspace →L[ℂ] evenSubspace} (hK : IsSoninPrincipalRelativeIdeal K) :
    soninFinitePartₗ (hp := hp) ha hinj
        ⟨K, relative_mem_soninPrincipalRelativeRange a p hp hK⟩ = opTrace K := by
  rw [soninFinitePartₗ_apply,
    soninFinitePartOfMem_eq ha hinj _ ⟨0, K, hK⟩ (by simp [toOperator])]
  simp [finitePart]

/-- Every presented operator splits inside the subspace into its shell and its correction. -/
theorem soninPrincipalRelativeRange_eq_shell_add_relative
    (T : soninPrincipalRelativeRange a p hp)
    (X : SoninPrincipalRelativePresentation a p hp)
    (hX : toOperator X = (T : evenSubspace →L[ℂ] evenSubspace)) :
    T = ⟨finitePrimeSoninPrincipalShellCombination a p hp X.coefficient,
          shell_mem_soninPrincipalRelativeRange a p hp X.coefficient⟩ +
        ⟨X.relative, relative_mem_soninPrincipalRelativeRange a p hp X.relative_mem⟩ := by
  apply Subtype.ext
  rw [Submodule.coe_add, ← hX, toOperator]

/-- **Uniqueness of the signed finite part.**  A linear functional on the presented operators
whose principal value is the logarithmic orbital trace and whose relative value is the ordinary
trace is the signed finite part. -/
theorem eq_soninFinitePartₗ_of_normalizations (ha : 0 < a) (hinj : Function.Injective p)
    (F : soninPrincipalRelativeRange a p hp →ₗ[ℂ] ℂ)
    (hshell : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      F ⟨finitePrimeSoninPrincipalShellCombination a p hp A,
        shell_mem_soninPrincipalRelativeRange a p hp A⟩ = principalTrace p A)
    (hrelative : ∀ (K : evenSubspace →L[ℂ] evenSubspace)
      (hK : IsSoninPrincipalRelativeIdeal K),
      F ⟨K, relative_mem_soninPrincipalRelativeRange a p hp hK⟩ = opTrace K) :
    F = soninFinitePartₗ ha hinj := by
  ext T
  obtain ⟨X, hX⟩ := T.2
  rw [soninPrincipalRelativeRange_eq_shell_add_relative T X hX, F.map_add,
    (soninFinitePartₗ ha hinj).map_add, hshell, hrelative X.relative X.relative_mem,
    soninFinitePartₗ_shell ha hinj X.coefficient,
    soninFinitePartₗ_relative ha hinj X.relative_mem]

/-- **Existence and uniqueness together.** -/
theorem existsUnique_soninFinitePart (ha : 0 < a) (hinj : Function.Injective p) :
    ∃! F : soninPrincipalRelativeRange a p hp →ₗ[ℂ] ℂ,
      (∀ A : Matrix (Fin n) (Fin n) ℂ,
          F ⟨finitePrimeSoninPrincipalShellCombination a p hp A,
            shell_mem_soninPrincipalRelativeRange a p hp A⟩ = principalTrace p A) ∧
        ∀ (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsSoninPrincipalRelativeIdeal K),
          F ⟨K, relative_mem_soninPrincipalRelativeRange a p hp hK⟩ = opTrace K := by
  refine ⟨soninFinitePartₗ ha hinj,
    ⟨fun A => soninFinitePartₗ_shell ha hinj A, fun K hK => soninFinitePartₗ_relative ha hinj hK⟩,
    ?_⟩
  rintro F ⟨hshell, hrelative⟩
  exact eq_soninFinitePartₗ_of_normalizations ha hinj F hshell hrelative

/-- The same uniqueness read against a linear functional on all bounded operators: it agrees with
the signed finite part on every presented operator. -/
theorem apply_toOperator_eq_finitePart
    (F : (evenSubspace →L[ℂ] evenSubspace) →ₗ[ℂ] ℂ)
    (hshell : ∀ A : Matrix (Fin n) (Fin n) ℂ,
      F (finitePrimeSoninPrincipalShellCombination a p hp A) = principalTrace p A)
    (hrelative : ∀ K : evenSubspace →L[ℂ] evenSubspace,
      IsSoninPrincipalRelativeIdeal K → F K = opTrace K)
    (X : SoninPrincipalRelativePresentation a p hp) :
    F (toOperator X) = finitePart X := by
  rw [toOperator, F.map_add, hshell, hrelative X.relative X.relative_mem, finitePart]

section GramLinearity

variable (a : ℝ) (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime)

@[simp]
theorem finitePrimeSoninQuadraticCornerCombination_zero :
    finitePrimeSoninQuadraticCornerCombination a p hp 0 = 0 := by
  classical
  unfold finitePrimeSoninQuadraticCornerCombination
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.zero_apply]
  exact ContinuousLinearMap.ext fun x => by simp

theorem finitePrimeSoninQuadraticCornerCombination_add
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninQuadraticCornerCombination a p hp (A + B) =
      finitePrimeSoninQuadraticCornerCombination a p hp A +
        finitePrimeSoninQuadraticCornerCombination a p hp B := by
  classical
  unfold finitePrimeSoninQuadraticCornerCombination
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.add_apply]
  refine ContinuousLinearMap.ext fun x => ?_
  exact add_smul (A i j) (B i j)
    ((evenCentralSoninQuadraticCorner a (p i : ℝ) (p j : ℝ)
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt)) x)

theorem finitePrimeSoninQuadraticCornerCombination_smul
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePrimeSoninQuadraticCornerCombination a p hp (c • A) =
      c • finitePrimeSoninQuadraticCornerCombination a p hp A := by
  classical
  unfold finitePrimeSoninQuadraticCornerCombination
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply]
  exact mul_smul c (A i j)
    (evenCentralSoninQuadraticCorner a (p i : ℝ) (p j : ℝ)
      (by exact_mod_cast (hp i).one_lt) (by exact_mod_cast (hp j).one_lt))

/-- The exact finite-place anomaly: the ordinary trace of the residual between the actual prime
Gram combination and its principal shell. -/
def soninFinitePrimeAnomaly (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  opTrace (finitePrimeSoninQuadraticCornerCombination a p hp A -
    finitePrimeSoninPrincipalShellCombination a p hp A)

@[simp] theorem soninFinitePrimeAnomaly_zero : soninFinitePrimeAnomaly a p hp 0 = 0 := by
  simp [soninFinitePrimeAnomaly]

/-- The anomaly is additive in the coefficient matrix. -/
theorem soninFinitePrimeAnomaly_add (ha : 0 < a) (A B : Matrix (Fin n) (Fin n) ℂ) :
    soninFinitePrimeAnomaly a p hp (A + B) =
      soninFinitePrimeAnomaly a p hp A + soninFinitePrimeAnomaly a p hp B := by
  have hA := finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination a ha p hp A
  have hB := finitePrimeSoninQuadraticCorner_principalRelativeEq_shellCombination a ha p hp B
  have hsplit : finitePrimeSoninQuadraticCornerCombination a p hp (A + B) -
      finitePrimeSoninPrincipalShellCombination a p hp (A + B) =
      (finitePrimeSoninQuadraticCornerCombination a p hp A -
          finitePrimeSoninPrincipalShellCombination a p hp A) +
        (finitePrimeSoninQuadraticCornerCombination a p hp B -
          finitePrimeSoninPrincipalShellCombination a p hp B) := by
    rw [finitePrimeSoninQuadraticCornerCombination_add,
      finitePrimeSoninPrincipalShellCombination_add]
    abel
  rw [soninFinitePrimeAnomaly, hsplit,
    opTrace_add_of_memSchattenClass_one hA.memSchattenClass_one hB.memSchattenClass_one]
  rfl

/-- The anomaly is homogeneous in the coefficient matrix. -/
theorem soninFinitePrimeAnomaly_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    soninFinitePrimeAnomaly a p hp (c • A) = c * soninFinitePrimeAnomaly a p hp A := by
  have hsplit : finitePrimeSoninQuadraticCornerCombination a p hp (c • A) -
      finitePrimeSoninPrincipalShellCombination a p hp (c • A) =
      c • (finitePrimeSoninQuadraticCornerCombination a p hp A -
        finitePrimeSoninPrincipalShellCombination a p hp A) := by
    rw [finitePrimeSoninQuadraticCornerCombination_smul,
      finitePrimeSoninPrincipalShellCombination_smul, smul_sub]
  rw [soninFinitePrimeAnomaly, hsplit, opTrace_smul]
  rfl

end GramLinearity

/-- **The finite part of an actual Gram combination.**  Logarithmic orbital trace plus the exact
anomaly. -/
theorem finitePart_ofQuadraticCorner_eq_anomaly (ha : 0 < a)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    finitePart (ofQuadraticCorner (p := p) (hp := hp) ha A) =
      principalTrace p A + soninFinitePrimeAnomaly a p hp A := rfl

/-- The unique functional evaluates the actual Gram combination as orbital trace plus anomaly. -/
theorem soninFinitePartₗ_quadraticCorner (ha : 0 < a) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    soninFinitePartₗ (hp := hp) ha hinj
        ⟨finitePrimeSoninQuadraticCornerCombination a p hp A,
          (toOperator_ofQuadraticCorner (p := p) (hp := hp) ha A) ▸
            toOperator_mem_soninPrincipalRelativeRange
              (ofQuadraticCorner (p := p) (hp := hp) ha A)⟩ =
      principalTrace p A + soninFinitePrimeAnomaly a p hp A := by
  rw [soninFinitePartₗ_apply,
    soninFinitePartOfMem_eq ha hinj _ (ofQuadraticCorner (p := p) (hp := hp) ha A)
      (toOperator_ofQuadraticCorner (p := p) (hp := hp) ha A)]
  rfl

end RHTower
