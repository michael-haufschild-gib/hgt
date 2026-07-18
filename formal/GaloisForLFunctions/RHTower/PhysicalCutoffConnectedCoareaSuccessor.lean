import GaloisForLFunctions.RHTower.PhysicalCutoffConnectedCoarea

/-!
# Ordinary-successor shells of the connected physical-cutoff recursion

Differencing the physical-cutoff Boolean sums in the integer cutoff `H` isolates the *equality
shell*: the subsets whose scaled conductor is exactly `H + 1`.  Two structural consequences follow.

* **Single-face localization.**  When the subset-product map is injective — which happens for a
  finite set of distinct ordinary primes, by unique factorization — an equality shell carries at
  most one Boolean face.  There is no `2 ^ |s|` within-shell multiplicity.
* **The stationary affine mode.**  The complete survival product `∏ (1 - θ p)` is annihilated by
  the cutoff difference, and inside the affine span of the low sum and the oriented high field it
  spans the *entire* kernel.  Consequently it cannot be produced by successor telescoping, and no
  uniformly bounded primitive can absorb it over a cofinal aperture.

The low/high cutoff sums, the oriented coarea field, the joined trace and the survival-product
classification are taken from `PhysicalCutoffConnectedCoarea`.
-/

open scoped BigOperators

namespace RHTower

variable {R ι : Type*}

/-! ## The equality shell -/

/-- Signed Boolean shell of subsets whose scaled conductor is exactly `H + 1`.  This is the exact
increment of both cutoff sums. -/
def aliasEqualityShell [CommRing R] (q : ℕ) (s : Finset ℕ) (ν : ℕ → R) (H : ℕ) : R :=
  ∑ t ∈ s.powerset,
    if q * ∏ p ∈ t, p = H + 1 then (-1 : R) ^ t.card * ∏ p ∈ t, ν p else 0

/-- The low cutoff sum increases by exactly the equality shell. -/
theorem truncatedAliasSum_succ_sub [CommRing R] (q H : ℕ) (s : Finset ℕ) (ν : ℕ → R) :
    truncatedAliasSum q s ν (H + 1) - truncatedAliasSum q s ν H = aliasEqualityShell q s ν H := by
  unfold truncatedAliasSum aliasEqualityShell
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hle : q * ∏ p ∈ t, p ≤ H
  · have h1 : q * ∏ p ∈ t, p ≤ H + 1 := hle.trans (Nat.le_succ H)
    have h2 : ¬ q * ∏ p ∈ t, p = H + 1 := by omega
    simp [hle, h1, h2]
  · by_cases heq : q * ∏ p ∈ t, p = H + 1
    · simp [heq]
    · have h1 : ¬ q * ∏ p ∈ t, p ≤ H + 1 := by omega
      simp [hle, h1, heq]

/-- The high cutoff tail decreases by exactly the equality shell. -/
theorem truncatedAliasHighSum_succ_sub [CommRing R] (q H : ℕ) (s : Finset ℕ) (ν : ℕ → R) :
    truncatedAliasHighSum q s ν H - truncatedAliasHighSum q s ν (H + 1) =
      aliasEqualityShell q s ν H := by
  unfold truncatedAliasHighSum aliasEqualityShell
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hlt : H < q * ∏ p ∈ t, p
  · by_cases heq : q * ∏ p ∈ t, p = H + 1
    · simp [heq]
    · have h1 : H + 1 < q * ∏ p ∈ t, p := by omega
      simp [hlt, h1, heq]
  · have h1 : ¬ H + 1 < q * ∏ p ∈ t, p := by omega
    have h2 : ¬ q * ∏ p ∈ t, p = H + 1 := by omega
    simp [hlt, h1, h2]

/-- The oriented coarea field increases by exactly the equality shell of the incidence
coordinates. -/
theorem physicalCutoffCoareaField_succ_sub [CommRing R] (q H : ℕ) (s : Finset ℕ)
    (χ : ℕ → ι → R) (x : ι) :
    physicalCutoffCoareaField q (H + 1) s χ x - physicalCutoffCoareaField q H s χ x =
      aliasEqualityShell q s (fun p => χ p x) H := by
  unfold physicalCutoffCoareaField
  rw [← truncatedAliasHighSum_succ_sub q H s fun p => χ p x]
  ring

/-- **Joined-trace successor law.**  The cutoff increment of the joined trace is the density shell
weighted by `J`, minus the observation functional applied to the incidence shell. -/
theorem physicalCutoffCoareaTrace_succ_sub [CommRing R] (q H : ℕ) (s : Finset ℕ)
    (χ : ℕ → ι → R) (θ : ℕ → R) (u : Finset ι) (weight : ι → R) (J : R) :
    physicalCutoffCoareaTrace q (H + 1) s χ θ u weight J -
        physicalCutoffCoareaTrace q H s χ θ u weight J =
      J * aliasEqualityShell q s θ H -
        ∑ x ∈ u, weight x * aliasEqualityShell q s (fun p => χ p x) H := by
  unfold physicalCutoffCoareaTrace
  have hlow := truncatedAliasSum_succ_sub q H s θ
  have hfield : ∀ x : ι, physicalCutoffCoareaField q (H + 1) s χ x =
      physicalCutoffCoareaField q H s χ x + aliasEqualityShell q s (fun p => χ p x) H := by
    intro x
    have := physicalCutoffCoareaField_succ_sub q H s χ x
    linear_combination this
  have hsum : ∑ x ∈ u, weight x * physicalCutoffCoareaField q (H + 1) s χ x =
      (∑ x ∈ u, weight x * physicalCutoffCoareaField q H s χ x) +
        ∑ x ∈ u, weight x * aliasEqualityShell q s (fun p => χ p x) H := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hfield x]
    ring
  rw [hsum]
  linear_combination J * hlow

/-! ## Connected prime-adjunction forcing -/

/-- The connected incidence/coarea forcing produced by adjoining one fresh prime coordinate.  This
is the exact source term appearing in `physicalCutoffCoareaTrace_insert`. -/
def connectedCoareaForcing [CommRing R] (q p H : ℕ) (s : Finset ℕ)
    (χ : ℕ → ι → R) (θ : ℕ → R) (u : Finset ι) (weight : ι → R) : R :=
  ∑ x ∈ u, weight x * (χ p x - θ p) * physicalCutoffCoareaField (q * p) H s χ x

/-- Adjoining the fresh coordinate to the joined trace produces exactly the connected forcing. -/
theorem physicalCutoffCoareaTrace_insert_eq_forcing [CommRing R]
    {q p H : ℕ} {s : Finset ℕ} (hp : p ∉ s)
    (χ : ℕ → ι → R) (θ : ℕ → R) (u : Finset ι) (weight : ι → R) (J : R) :
    physicalCutoffCoareaTrace q H (insert p s) χ θ u weight J =
      physicalCutoffCoareaTrace q H s χ θ u weight J -
        θ p * physicalCutoffCoareaTrace (q * p) H s χ θ u weight J +
        connectedCoareaForcing q p H s χ θ u weight :=
  physicalCutoffCoareaTrace_insert hp χ θ u weight J

/-- **Mixed prime/successor Stokes law.**  The cutoff increment of the connected forcing is the
forcing weight applied to the contracted equality shell. -/
theorem connectedCoareaForcing_succ_sub [CommRing R] (q p H : ℕ) (s : Finset ℕ)
    (χ : ℕ → ι → R) (θ : ℕ → R) (u : Finset ι) (weight : ι → R) :
    connectedCoareaForcing q p (H + 1) s χ θ u weight -
        connectedCoareaForcing q p H s χ θ u weight =
      ∑ x ∈ u, weight x * (χ p x - θ p) * aliasEqualityShell (q * p) s (fun r => χ r x) H := by
  unfold connectedCoareaForcing
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have := physicalCutoffCoareaField_succ_sub (q * p) H s χ x
  linear_combination (weight x * (χ p x - θ p)) * this

/-! ## Single-face localization -/

/-- If no subset meets the shell condition the shell vanishes. -/
theorem aliasEqualityShell_eq_zero [CommRing R] {q H : ℕ} {s : Finset ℕ} (ν : ℕ → R)
    (hno : ∀ t ∈ s.powerset, q * ∏ p ∈ t, p ≠ H + 1) :
    aliasEqualityShell q s ν H = 0 := by
  unfold aliasEqualityShell
  refine Finset.sum_eq_zero fun t ht => ?_
  simp [hno t ht]

/-- Under injectivity of the subset-product map, a witnessed shell is exactly one signed face. -/
theorem aliasEqualityShell_eq_single [CommRing R] {q H : ℕ} {s : Finset ℕ} (ν : ℕ → R)
    (hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (s.powerset : Set (Finset ℕ)))
    {t : Finset ℕ} (ht : t ∈ s.powerset) (hcond : q * ∏ p ∈ t, p = H + 1) :
    aliasEqualityShell q s ν H = (-1 : R) ^ t.card * ∏ p ∈ t, ν p := by
  unfold aliasEqualityShell
  rw [Finset.sum_eq_single t]
  · simp [hcond]
  · intro b hb hbt
    have hne : q * ∏ p ∈ b, p ≠ H + 1 := by
      intro hbcond
      exact hbt (hinj hb ht (by
        have : q * ∏ p ∈ b, p = q * ∏ p ∈ t, p := by rw [hbcond, hcond]
        rcases Nat.eq_zero_or_pos q with hq | hq
        · subst hq
          simp at hbcond
        · exact Nat.eq_of_mul_eq_mul_left hq this))
    simp [hne]
  · intro hnot
    exact absurd ht hnot

/-- **Single-face shell theorem.**  Under subset-product injectivity every ordinary-successor shell
either vanishes or is one centered signed face.  There is no within-shell Boolean multiplicity. -/
theorem aliasEqualityShell_single_face [CommRing R] (q H : ℕ) (s : Finset ℕ) (ν : ℕ → R)
    (hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (s.powerset : Set (Finset ℕ))) :
    aliasEqualityShell q s ν H = 0 ∨
      ∃ t ∈ s.powerset, q * ∏ p ∈ t, p = H + 1 ∧
        aliasEqualityShell q s ν H = (-1 : R) ^ t.card * ∏ p ∈ t, ν p := by
  by_cases hex : ∃ t ∈ s.powerset, q * ∏ p ∈ t, p = H + 1
  · obtain ⟨t, ht, hcond⟩ := hex
    exact Or.inr ⟨t, ht, hcond, aliasEqualityShell_eq_single ν hinj ht hcond⟩
  · simp only [not_exists, not_and] at hex
    exact Or.inl (aliasEqualityShell_eq_zero ν hex)

/-- Unique factorization: on subsets of a finite set of distinct primes the product map is
injective. -/
theorem prod_injOn_of_prime {s : Finset ℕ} (hprime : ∀ p ∈ s, p.Prime) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) (s.powerset : Set (Finset ℕ)) := by
  intro t ht u hu hprod
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at ht hu
  have key : ∀ (v w : Finset ℕ), v ⊆ s → w ⊆ s → (∏ p ∈ v, p) = (∏ p ∈ w, p) →
      ∀ r ∈ v, r ∈ w := by
    intro v w hv hw hvw r hr
    have hrp : r.Prime := hprime r (hv hr)
    have hdvd : r ∣ ∏ p ∈ w, p := by
      rw [← hvw]
      exact Finset.dvd_prod_of_mem _ hr
    obtain ⟨c, hc, hrc⟩ := (Nat.Prime.prime hrp).dvd_finsetProd_iff _ |>.mp hdvd
    have hcp : c.Prime := hprime c (hw hc)
    have : r = c := ((Nat.prime_dvd_prime_iff_eq hrp hcp).mp hrc)
    rwa [this]
  ext r
  exact ⟨fun hr => key t u ht hu hprod r hr, fun hr => key u t hu ht hprod.symm r hr⟩

/-- **Ordinary single-face law.**  For distinct ordinary primes every successor shell holds at most
one Boolean face. -/
theorem aliasEqualityShell_single_face_of_prime [CommRing R] (q H : ℕ) (s : Finset ℕ)
    (ν : ℕ → R) (hprime : ∀ p ∈ s, p.Prime) :
    aliasEqualityShell q s ν H = 0 ∨
      ∃ t ∈ s.powerset, q * ∏ p ∈ t, p = H + 1 ∧
        aliasEqualityShell q s ν H = (-1 : R) ^ t.card * ∏ p ∈ t, ν p :=
  aliasEqualityShell_single_face q H s ν (prod_injOn_of_prime hprime)

/-- The face sign of a squarefree ordinary modulus is its Moebius value. -/
theorem moebius_prod_eq_neg_one_pow {t : Finset ℕ} (hprime : ∀ p ∈ t, p.Prime) :
    ArithmeticFunction.moebius (∏ p ∈ t, p) = (-1 : ℤ) ^ t.card := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert p t hp ih =>
      have hpp : p.Prime := hprime p (Finset.mem_insert_self p t)
      have htp : ∀ r ∈ t, r.Prime := fun r hr => hprime r (Finset.mem_insert_of_mem hr)
      have hcop : Nat.Coprime p (∏ r ∈ t, r) := by
        refine Nat.Coprime.prod_right fun r hr => ?_
        have hrp : r.Prime := htp r hr
        have hne : p ≠ r := fun h => hp (h ▸ hr)
        exact (Nat.coprime_primes hpp hrp).mpr hne
      rw [Finset.prod_insert hp, Finset.card_insert_of_notMem hp,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hpp, ih htp]
      ring

/-! ## The stationary survival mode -/

/-- The affine drift is annihilated by the cutoff difference: the complete survival product lies in
the kernel of the ordinary-successor derivative. -/
theorem physicalCutoffCoareaAffineDrift_succ_sub [CommRing R] (q H : ℕ) (s : Finset ℕ)
    (θ : ℕ → R) :
    physicalCutoffCoareaAffineDrift q (H + 1) s θ - physicalCutoffCoareaAffineDrift q H s θ = 0 := by
  rw [physicalCutoffCoareaAffineDrift_eq_neg_survival,
    physicalCutoffCoareaAffineDrift_eq_neg_survival, sub_self]

/-- Cutoff increment of a general affine combination of the oriented high field and the low sum.
Both differ by the same shell, so only the sum of the coefficients survives. -/
theorem affineCutoffCombination_succ_sub [CommRing R] (q H : ℕ) (s : Finset ℕ) (θ : ℕ → R)
    (α β : R) :
    (α * -truncatedAliasHighSum q s θ (H + 1) + β * truncatedAliasSum q s θ (H + 1)) -
        (α * -truncatedAliasHighSum q s θ H + β * truncatedAliasSum q s θ H) =
      (α + β) * aliasEqualityShell q s θ H := by
  have hhigh := truncatedAliasHighSum_succ_sub q H s θ
  have hlow := truncatedAliasSum_succ_sub q H s θ
  linear_combination α * hhigh + β * hlow

/-- The shell just below the base conductor is the empty face, hence equal to `1` for distinct
primes.  This is the nonvanishing witness that pins the stationary line. -/
theorem aliasEqualityShell_base [CommRing R] {q : ℕ} (hq : 1 ≤ q) (s : Finset ℕ) (ν : ℕ → R)
    (hprime : ∀ p ∈ s, p.Prime) :
    aliasEqualityShell q s ν (q - 1) = 1 := by
  have hcond : q * ∏ p ∈ (∅ : Finset ℕ), p = (q - 1) + 1 := by
    simp
    omega
  have hmem : (∅ : Finset ℕ) ∈ s.powerset := Finset.empty_mem_powerset s
  rw [aliasEqualityShell_eq_single ν (prod_injOn_of_prime hprime) hmem hcond]
  simp

/-- **Uniqueness of the stationary affine mode.**  An affine combination of the oriented high field
and the low sum is cutoff-stationary for every cutoff exactly on the line `β = -α`, which is
generated by the negative complete survival product. -/
theorem affineCutoffCombination_stationary_iff [CommRing R] {q : ℕ} (hq : 1 ≤ q) (s : Finset ℕ)
    (θ : ℕ → R) (hprime : ∀ p ∈ s, p.Prime) (α β : R) :
    (∀ H, (α * -truncatedAliasHighSum q s θ (H + 1) + β * truncatedAliasSum q s θ (H + 1)) -
        (α * -truncatedAliasHighSum q s θ H + β * truncatedAliasSum q s θ H) = 0) ↔
      β = -α := by
  constructor
  · intro h
    have hbase := h (q - 1)
    rw [affineCutoffCombination_succ_sub q (q - 1) s θ α β,
      aliasEqualityShell_base hq s θ hprime, mul_one] at hbase
    linear_combination hbase
  · intro h H
    rw [affineCutoffCombination_succ_sub q H s θ α β, h]
    simp

/-! ## The quadratic even-gap survival ramp -/

/-- **The even-gap ramp is a stationary mode, not successor curvature.**  For quadratic-root
densities on distinct prime coordinates with `2` active and an even gap, the affine drift is
simultaneously annihilated by every cutoff difference and nonzero. -/
theorem quadraticSurvivalRamp_stationary_and_ne_zero
    (q : ℕ) (s : Finset ℕ) (hprime : ∀ p ∈ s, p.Prime) (h : ℤ) (heven : (2 : ℤ) ∣ h) :
    (∀ H : ℕ, physicalCutoffCoareaAffineDrift q (H + 1) s
        (fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ)) -
      physicalCutoffCoareaAffineDrift q H s
        (fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ)) = 0) ∧
      ∀ H : ℕ, physicalCutoffCoareaAffineDrift q H s
        (fun n => (quadraticCongruenceRootCountTotal n h : ℂ) / (n : ℂ)) ≠ 0 := by
  refine ⟨fun H => physicalCutoffCoareaAffineDrift_succ_sub q H s _, fun H => ?_⟩
  intro hzero
  have := (quadraticCongruencePhysicalCutoffAffineDrift_eq_zero_iff q H s hprime h).mp hzero
  exact this.2 heven

/-! ## No bounded successor primitive -/

/-- **Exact primitive growth.**  A successor primitive of a constant ramp grows linearly. -/
theorem primitive_growth_of_constant_step [CommRing R] (Ψ : ℕ → R) (V : R) {H₀ H₁ : ℕ}
    (hle : H₀ ≤ H₁) (hstep : ∀ H, H₀ ≤ H → H < H₁ → Ψ (H + 1) - Ψ H = -V) :
    Ψ H₁ - Ψ H₀ = -((H₁ - H₀ : ℕ) : R) * V := by
  induction H₁, hle using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hstep' : ∀ H, H₀ ≤ H → H < n → Ψ (H + 1) - Ψ H = -V := fun H h1 h2 =>
        hstep H h1 (h2.trans (Nat.lt_succ_self n))
      have hlast : Ψ (n + 1) - Ψ n = -V := hstep n hn (Nat.lt_succ_self n)
      have hcast : ((n + 1 - H₀ : ℕ) : R) = ((n - H₀ : ℕ) : R) + 1 := by
        have : n + 1 - H₀ = (n - H₀) + 1 := by omega
        rw [this]
        push_cast
        ring
      rw [hcast]
      have := ih hstep'
      linear_combination this + hlast

/-- **No uniformly bounded successor primitive.**  A nonzero stationary ramp cannot be written as a
successor coboundary of a bounded primitive over a cofinal aperture. -/
theorem no_bounded_primitive_of_ne_zero (Ψ : ℕ → ℂ) (V : ℂ) (hV : V ≠ 0) (H₀ : ℕ) (M : ℝ)
    (hbound : ∀ H, ‖Ψ H‖ ≤ M) (hstep : ∀ H, H₀ ≤ H → Ψ (H + 1) - Ψ H = -V) : False := by
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * M) / ‖V‖)
  have hle : H₀ ≤ H₀ + N := Nat.le_add_right H₀ N
  have hgrow : Ψ (H₀ + N) - Ψ H₀ = -((H₀ + N - H₀ : ℕ) : ℂ) * V :=
    primitive_growth_of_constant_step Ψ V hle fun H h1 _ => hstep H h1
  have hidx : H₀ + N - H₀ = N := by omega
  rw [hidx] at hgrow
  have hnorm : ‖Ψ (H₀ + N) - Ψ H₀‖ = (N : ℝ) * ‖V‖ := by
    rw [hgrow]
    simp
  have hupper : ‖Ψ (H₀ + N) - Ψ H₀‖ ≤ 2 * M := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := hbound (H₀ + N)
    have h2 := hbound H₀
    linarith
  rw [hnorm] at hupper
  have hlow : (2 * M) / ‖V‖ * ‖V‖ < (N : ℝ) * ‖V‖ :=
    mul_lt_mul_of_pos_right hN hVpos
  rw [div_mul_cancel₀ _ (ne_of_gt hVpos)] at hlow
  linarith

end RHTower
