import GaloisForLFunctions.RHTower.Sieve.VinogradovReservoirRecurrence

/-!
# Colliding blocks lose a pair of variables

A non-injective block `x : Fin a → Fin N` has two coordinates `x i = x j = y`.  Its power
signature is the signature of the pair `(y, y)` plus the signature of the remaining `a - 2`
coordinates.  Removing the pair maps every colliding completion injectively to a witness pair, a
pair of repeated values and a pair of tuples of length `a - 2 + b` whose signatures differ by a
fixed translate.  The translate costs nothing (`card_vinogradovFixedBlocks_le_finiteFiberEnergy`), so

`#colliding completions ≤ (a² - a)² N² J_{a-2+b}(N)`

(`card_vinogradovCollidingBlockCompletion_le_pairRemoval`).  In the moment recursion this replaces
the factor `N^{2(a-1)} J_b(N)` by `N² J_{a-2+b}(N)`
(`vinogradov_moment_bertrand_recurrence_pairRemoval`).
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- The coordinates other than the two coordinates of a collision witness. -/
abbrev VinogradovWitnessComplement {a : ℕ} (w : VinogradovCollisionWitness a) :=
  {c : Fin a // c ≠ w.1.1 ∧ c ≠ w.1.2}

theorem card_vinogradovWitnessComplement {a : ℕ} (w : VinogradovCollisionWitness a) :
    Fintype.card (VinogradovWitnessComplement w) = a - 2 := by
  classical
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter fun c : Fin a => c ≠ w.1.1 ∧ c ≠ w.1.2) =
      Finset.univ \ {w.1.1, w.1.2} := by
    ext c
    simp [not_or]
  rw [hset, Finset.card_sdiff, Finset.inter_univ, Finset.card_pair w.2, Finset.card_univ,
    Fintype.card_fin]

/-- An enumeration of the complement of a collision witness. -/
def vinogradovWitnessComplementEquiv {a : ℕ} (w : VinogradovCollisionWitness a) :
    Fin (a - 2) ≃ VinogradovWitnessComplement w :=
  (Fintype.equivFinOfCardEq (card_vinogradovWitnessComplement w)).symm

/-- The block with the two witness coordinates removed. -/
def vinogradovPairRemoval {N a : ℕ} (w : VinogradovCollisionWitness a) (x : Fin a → Fin N) :
    Fin (a - 2) → Fin N :=
  fun m => x (vinogradovWitnessComplementEquiv w m).1

/-- The pair `(y, y)`. -/
def vinogradovRepeatedPair {N : ℕ} (y : Fin N) : Fin 2 → Fin N := fun _ => y

/-- Signature of a colliding block: the repeated pair plus the remaining coordinates. -/
theorem vinogradovPowerSignatureMod_eq_pair_add_removal {q k N a : ℕ}
    (w : VinogradovCollisionWitness a) (x : Fin a → Fin N) (hx : x w.1.1 = x w.1.2) :
    vinogradovPowerSignatureMod q k x =
      vinogradovPowerSignatureMod q k (vinogradovRepeatedPair (x w.1.1)) +
        vinogradovPowerSignatureMod q k (vinogradovPairRemoval w x) := by
  classical
  funext j
  simp only [vinogradovPowerSignatureMod, Pi.add_apply, vinogradovRepeatedPair, Fin.sum_univ_two]
  set f : Fin a → ZMod q := fun c => ((x c).val : ZMod q) ^ (j.val + 1) with hf
  have hi : w.1.1 ∈ (Finset.univ : Finset (Fin a)) := Finset.mem_univ _
  have hj : w.1.2 ∈ (Finset.univ : Finset (Fin a)).erase w.1.1 :=
    Finset.mem_erase.mpr ⟨fun h => w.2 h.symm, Finset.mem_univ _⟩
  have hsplit : ∑ c : Fin a, f c =
      f w.1.1 +
        (f w.1.2 + ∑ c ∈ ((Finset.univ : Finset (Fin a)).erase w.1.1).erase w.1.2, f c) := by
    rw [Finset.add_sum_erase _ _ hj, Finset.add_sum_erase _ _ hi]
  have hrest : ∑ c ∈ ((Finset.univ : Finset (Fin a)).erase w.1.1).erase w.1.2, f c =
      ∑ c : VinogradovWitnessComplement w, f c.1 := by
    apply Finset.sum_subtype
    intro c
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have henum : ∑ c : VinogradovWitnessComplement w, f c.1 =
      ∑ m : Fin (a - 2), f (vinogradovWitnessComplementEquiv w m).1 :=
    (Equiv.sum_comp (vinogradovWitnessComplementEquiv w) (fun c => f c.1)).symm
  change ∑ c : Fin a, f c = f w.1.1 + f w.1.1 +
    ∑ m : Fin (a - 2), f (vinogradovWitnessComplementEquiv w m).1
  rw [hsplit, hrest, henum]
  have h12 : f w.1.2 = f w.1.1 := by rw [hf]; simp only [hx]
  rw [h12, add_assoc]

/-- A colliding block is determined by its witness, its repeated value and the remaining
coordinates. -/
theorem eq_of_pairRemoval_eq {N a : ℕ} (w : VinogradovCollisionWitness a)
    {x x' : Fin a → Fin N} (hx : x w.1.1 = x w.1.2) (hx' : x' w.1.1 = x' w.1.2)
    (hy : x w.1.1 = x' w.1.1) (hr : vinogradovPairRemoval w x = vinogradovPairRemoval w x') :
    x = x' := by
  funext c
  by_cases hc1 : c = w.1.1
  · subst hc1
    exact hy
  by_cases hc2 : c = w.1.2
  · subst hc2
    rw [← hx, ← hx', hy]
  · have h := congrFun hr ((vinogradovWitnessComplementEquiv w).symm ⟨c, hc1, hc2⟩)
    simpa [vinogradovPairRemoval] using h

/-- A collision witness of a non-injective block. -/
def vinogradovNoninjectiveWitness {N a : ℕ} (x : VinogradovNoninjectiveBlock N a) :
    VinogradovCollisionWitness a :=
  ⟨(Classical.choose (Function.not_injective_iff.mp x.2),
      Classical.choose (Classical.choose_spec (Function.not_injective_iff.mp x.2))),
    (Classical.choose_spec (Classical.choose_spec (Function.not_injective_iff.mp x.2))).2⟩

theorem vinogradovNoninjectiveWitness_spec {N a : ℕ} (x : VinogradovNoninjectiveBlock N a) :
    x.1 (vinogradovNoninjectiveWitness x).1.1 = x.1 (vinogradovNoninjectiveWitness x).1.2 :=
  (Classical.choose_spec (Classical.choose_spec (Function.not_injective_iff.mp x.2))).1

/-- The reduced data of a colliding completion: witnesses, repeated values and the remaining
tuples. -/
abbrev VinogradovPairRemovalData (q N a b k : ℕ) :=
  {z : (VinogradovCollisionWitness a × VinogradovCollisionWitness a) × (Fin N × Fin N) ×
      ((Fin (a - 2 + b) → Fin N) × (Fin (a - 2 + b) → Fin N)) //
    vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair z.2.1.1) z.2.2.1) =
      vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair z.2.1.2) z.2.2.2)}

theorem card_vinogradovPairRemovalData_le {q N a b k : ℕ} [NeZero q] :
    Fintype.card (VinogradovPairRemovalData q N a b k) ≤
      (a * a - a) ^ (2 : ℕ) * N ^ (2 : ℕ) *
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k : (Fin (a - 2 + b) → Fin N) → Fin k → ZMod q) := by
  classical
  set E := finiteFiberEnergy
    (vinogradovPowerSignatureMod q k : (Fin (a - 2 + b) → Fin N) → Fin k → ZMod q)
  have e := Equiv.subtypeProdEquivSigmaSubtype
    (fun (ww : VinogradovCollisionWitness a × VinogradovCollisionWitness a)
      (z : (Fin N × Fin N) × ((Fin (a - 2 + b) → Fin N) × (Fin (a - 2 + b) → Fin N))) =>
      vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair z.1.1) z.2.1) =
        vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair z.1.2) z.2.2))
  rw [Fintype.card_congr e, Fintype.card_sigma]
  calc
    ∑ ww : VinogradovCollisionWitness a × VinogradovCollisionWitness a,
        Fintype.card {z : (Fin N × Fin N) ×
            ((Fin (a - 2 + b) → Fin N) × (Fin (a - 2 + b) → Fin N)) //
          vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair z.1.1) z.2.1) =
            vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair z.1.2) z.2.2)}
        ≤ ∑ _ww : VinogradovCollisionWitness a × VinogradovCollisionWitness a, N ^ (2 : ℕ) * E := by
      apply Finset.sum_le_sum
      intro ww _
      have e2 := Equiv.subtypeProdEquivSigmaSubtype
        (fun (yy : Fin N × Fin N)
          (z : (Fin (a - 2 + b) → Fin N) × (Fin (a - 2 + b) → Fin N)) =>
          vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair yy.1) z.1) =
            vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair yy.2) z.2))
      rw [Fintype.card_congr e2, Fintype.card_sigma]
      calc
        ∑ yy : Fin N × Fin N, Fintype.card {z : (Fin (a - 2 + b) → Fin N) ×
              (Fin (a - 2 + b) → Fin N) //
            vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair yy.1) z.1) =
              vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair yy.2) z.2)}
            ≤ ∑ _yy : Fin N × Fin N, E := by
          apply Finset.sum_le_sum
          intro yy _
          exact card_vinogradovFixedBlocks_le_finiteFiberEnergy _ _
        _ = N ^ (2 : ℕ) * E := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
            pow_two]
    _ = (a * a - a) ^ (2 : ℕ) * N ^ (2 : ℕ) * E := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, card_vinogradovCollisionWitness,
        smul_eq_mul]
      ring

/-- **Colliding completions lose a pair of variables.** -/
theorem card_vinogradovCollidingBlockCompletion_le_pairRemoval {q N k b : ℕ} [NeZero q] :
    Fintype.card (VinogradovCollidingBlockCompletion q N k b) ≤
      (k * k - k) ^ (2 : ℕ) * N ^ (2 : ℕ) *
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k : (Fin (k - 2 + b) → Fin N) → Fin k → ZMod q) := by
  classical
  refine le_trans ?_ card_vinogradovPairRemovalData_le
  let e := (Equiv.subtypeProdEquivSigmaSubtype
    (fun (xx : VinogradovNoninjectiveBlock N k × VinogradovNoninjectiveBlock N k)
      (uv : (Fin b → Fin N) × (Fin b → Fin N)) =>
      vinogradovPowerSignatureMod q k (Fin.append xx.1.1 uv.1) =
        vinogradovPowerSignatureMod q k (Fin.append xx.2.1 uv.2))).symm
  rw [Fintype.card_congr e]
  let red : VinogradovNoninjectiveBlock N k → (Fin b → Fin N) →
      VinogradovCollisionWitness k × Fin N × (Fin (k - 2 + b) → Fin N) := fun x u =>
    (vinogradovNoninjectiveWitness x, x.1 (vinogradovNoninjectiveWitness x).1.1,
      Fin.append (vinogradovPairRemoval (vinogradovNoninjectiveWitness x) x.1) u)
  have hsig : ∀ (x : VinogradovNoninjectiveBlock N k) (u : Fin b → Fin N),
      vinogradovPowerSignatureMod q k (Fin.append (vinogradovRepeatedPair (red x u).2.1)
          (red x u).2.2) = vinogradovPowerSignatureMod q k (Fin.append x.1 u) := by
    intro x u
    simp only [red]
    rw [vinogradovPowerSignatureMod_append, vinogradovPowerSignatureMod_append,
      vinogradovPowerSignatureMod_append,
      vinogradovPowerSignatureMod_eq_pair_add_removal (vinogradovNoninjectiveWitness x) x.1
        (vinogradovNoninjectiveWitness_spec x), add_assoc]
  have hred_inj : ∀ x x' u u', red x u = red x' u' → x = x' ∧ u = u' := by
    intro x x' u u' h
    simp only [red, Prod.mk.injEq] at h
    obtain ⟨hw, hy, happ⟩ := h
    have hr : vinogradovPairRemoval (vinogradovNoninjectiveWitness x) x.1 =
        vinogradovPairRemoval (vinogradovNoninjectiveWitness x') x'.1 := by
      funext m
      have := congrFun happ (Fin.castAdd b m)
      simpa only [Fin.append_left] using this
    have hu : u = u' := by
      funext m
      have := congrFun happ (Fin.natAdd (k - 2) m)
      simpa only [Fin.append_right] using this
    refine ⟨?_, hu⟩
    apply Subtype.ext
    have hspec := vinogradovNoninjectiveWitness_spec x
    have hspec' := vinogradovNoninjectiveWitness_spec x'
    rw [← hw] at hspec' hy hr
    exact eq_of_pairRemoval_eq _ hspec hspec' hy hr
  let F : {z : (VinogradovNoninjectiveBlock N k × VinogradovNoninjectiveBlock N k) ×
        ((Fin b → Fin N) × (Fin b → Fin N)) //
      vinogradovPowerSignatureMod q k (Fin.append z.1.1.1 z.2.1) =
        vinogradovPowerSignatureMod q k (Fin.append z.1.2.1 z.2.2)} →
      VinogradovPairRemovalData q N k b k := fun z =>
    ⟨(((red z.1.1.1 z.1.2.1).1, (red z.1.1.2 z.1.2.2).1),
      ((red z.1.1.1 z.1.2.1).2.1, (red z.1.1.2 z.1.2.2).2.1),
      ((red z.1.1.1 z.1.2.1).2.2, (red z.1.1.2 z.1.2.2).2.2)),
      (hsig z.1.1.1 z.1.2.1).trans (z.2.trans (hsig z.1.1.2 z.1.2.2).symm)⟩
  refine Fintype.card_le_of_injective F ?_
  intro z z' h
  simp only [F, Subtype.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨hw1, hw2⟩, ⟨hy1, hy2⟩, ⟨hr1, hr2⟩⟩ := h
  obtain ⟨hx1, hu1⟩ := hred_inj _ _ _ _ (Prod.ext hw1 (Prod.ext hy1 hr1))
  obtain ⟨hx2, hu2⟩ := hred_inj _ _ _ _ (Prod.ext hw2 (Prod.ext hy2 hr2))
  exact Subtype.ext (Prod.ext (Prod.ext hx1 hx2) (Prod.ext hu1 hu2))

/-- **Moment recursion with pair removal.** The injective leading blocks are covered by the
Bertrand reservoir exactly as in `vinogradov_moment_bertrand_recurrence`; the colliding ones cost
`(k² - k)² N² J_{k-2+b}(N)`. -/
theorem vinogradov_moment_bertrand_recurrence_pairRemoval
    {N k b : ℕ} (hk : k ≠ 0) (hb : b ≠ 0) (hN : N ≠ 0) :
    Fintype.card (VinogradovDiagonalSolution N (k + b) k) ≤
      2 * (vinogradovReservoirSize k *
          ∑ i : Fin (vinogradovReservoirSize k),
            (vinogradovReservoirPrime N k i) ^ (2 * b) *
              (N ^ k * (k.factorial *
                (vinogradovReservoirPrime N k i) ^ (k * (k - 1) / 2) *
                Fintype.card (VinogradovDiagonalSolution
                  (N ⌈/⌉ (vinogradovReservoirPrime N k i)) b k))) +
        (k * k - k) ^ (2 : ℕ) * N ^ (2 : ℕ) *
          Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k)) := by
  let q := vinogradovPrimeMomentModulus N k b
  have hqlarge := vinogradovPrimeMomentModulus_large N k b
  calc
    Fintype.card (VinogradovDiagonalSolution N (k + b) k) =
        finiteFiberEnergy
          (vinogradovPowerSignatureMod q k :
            (Fin (k + b) → Fin N) → Fin k → ZMod q) := by
      symm
      exact vinogradovModularMomentAt_eq_card_of_large hN hqlarge
    _ ≤ 2 * (finiteFiberEnergyWith
          (vinogradovSplitPowerSignature q N k b)
          (fun z => Function.Injective z.1) +
        Fintype.card (VinogradovCollidingBlockCompletion q N k b)) :=
      vinogradov_moment_collision_partition
    _ ≤ _ := by
      have hgood := vinogradov_injective_energy_reservoir_bound hk hb hN
      have hbad := card_vinogradovCollidingBlockCompletion_le_pairRemoval (q := q) (N := N)
        (k := k) (b := b)
      have hJ : finiteFiberEnergy
          (vinogradovPowerSignatureMod q k : (Fin (k - 2 + b) → Fin N) → Fin k → ZMod q) =
          Fintype.card (VinogradovDiagonalSolution N (k - 2 + b) k) := by
        apply vinogradovModularMomentAt_eq_card_of_large hN
        calc 2 * (k - 2 + b) * N ^ k ≤ 2 * (k + b) * N ^ k := by gcongr; omega
          _ < q := hqlarge
      rw [hJ] at hbad
      exact Nat.mul_le_mul_left 2 (Nat.add_le_add hgood hbad)

end

end RHTower.Sieve
