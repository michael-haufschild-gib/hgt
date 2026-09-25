import GaloisForLFunctions.RHTower.RouteEPrimitiveConeParentNoGo
import GaloisForLFunctions.RHTower.GibbsMoebiusAnchor

/-!
# All-grade parity barrier for the primitive Route E kernel

The literal primitive paired Gamma--Hankel kernel is asymptotically linear in its
small endpoint in the far cone.  Boolean insertion of any fixed finite set of
distinct primes therefore has leading coefficient `a * ∏ (1-p)`.  Its sign is
the parity of the number of inserted primes, at every finite grade.  The
one-prime forward payment from `RouteEPrimitiveConeParentNoGo` cannot become a
grade-stable local payment by adding finitely many more insertion levels.

This is a source-kernel obstruction, not a bound on the complete moving
Möbius covariance: the physical cutoff also contains all other grades and
denominator fibres.
-/

open Filter Topology

namespace RHTower

noncomputable section

private theorem primitive_scaled_limit (a : ℝ) :
    Tendsto (fun b : ℝ => b ^ 2 * routeEPrimitiveConeWeight a b) atTop (𝓝 a) := by
  have hc : ContinuousAt (fun u : ℝ =>
      a / ((1 + a * u) * (1 + 2 * a * u))) 0 := by
    apply ContinuousAt.div₀
    · fun_prop
    · fun_prop
    · norm_num
  have h := hc.tendsto.comp (tendsto_inv_atTop_zero :
    Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0))
  have h' : Tendsto (fun b : ℝ =>
      a / ((1 + a * b⁻¹) * (1 + 2 * a * b⁻¹))) atTop (𝓝 a) := by
    simpa [Function.comp_def] using h
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  dsimp [routeEPrimitiveConeWeight]
  field_simp [hb.ne']
  ring

private theorem tendsto_finset_sum_real {A X : Type*}
    {l : Filter A} (s : Finset X) (f : X → A → ℝ) (g : X → ℝ)
    (h : ∀ x ∈ s, Tendsto (f x) l (𝓝 (g x))) :
    Tendsto (fun y => ∑ x ∈ s, f x y) l (𝓝 (∑ x ∈ s, g x)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tendsto_const_nhds : Tendsto (fun _ : A => (0 : ℝ)) l (𝓝 0))
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      exact (h x (by simp)).add (ih (fun y hy => h y (by simp [hy])))

/-- Alternating full Boolean insertion of a fixed finite prime set into the
small endpoint of the actual primitive paired Gamma--Hankel kernel. -/
def routeEPrimitiveBooleanTransport (a b : ℝ) (P : Finset Nat.Primes) : ℝ :=
  ∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card *
    routeEPrimitiveConeWeight (a * ∏ p ∈ S, (p : ℝ)) b

/-- Exact all-grade far-cone coefficient.  The result is not obtained by
pairwise monotonicity: each new prime changes the leading sign. -/
theorem routeEPrimitiveBooleanTransport_scaled_limit (a : ℝ) (P : Finset Nat.Primes) :
    Tendsto (fun b : ℝ => b ^ 2 * routeEPrimitiveBooleanTransport a b P)
      atTop (𝓝 (a * ∏ p ∈ P, (1 - (p : ℝ)))) := by
  have hsum := tendsto_finset_sum_real P.powerset
    (fun S b => (-1 : ℝ) ^ S.card *
      (b ^ 2 * routeEPrimitiveConeWeight (a * ∏ p ∈ S, (p : ℝ)) b))
    (fun S => (-1 : ℝ) ^ S.card * (a * ∏ p ∈ S, (p : ℝ)))
    (by
      intro S hS
      exact tendsto_const_nhds.mul (primitive_scaled_limit _))
  have hfactor :
      (∑ S ∈ P.powerset,
        (-1 : ℝ) ^ S.card * (a * ∏ p ∈ S, (p : ℝ))) =
        a * ∏ p ∈ P, (1 - (p : ℝ)) := by
    have hp := (Finset.prod_sub (fun _ : Nat.Primes => (1 : ℝ))
      (fun p => (p : ℝ)) P).symm
    calc
      _ = a * (∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card *
          ∏ p ∈ S, (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        ring
      _ = a * ∏ p ∈ P, (1 - (p : ℝ)) := by
        congr 1
        simpa using hp
  rw [← hfactor]
  apply hsum.congr'
  exact Filter.Eventually.of_forall (fun b => by
    simp only [routeEPrimitiveBooleanTransport, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    ring)

private theorem signed_prime_survival_pos (P : Finset Nat.Primes) :
    0 < (-1 : ℝ) ^ P.card * ∏ p ∈ P, (1 - (p : ℝ)) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      have hprime : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.one_lt
      rw [Finset.card_insert_of_notMem hp, Finset.prod_insert hp, pow_succ]
      have heq : (-1 : ℝ) ^ P.card * -1 *
          ((1 - (p : ℝ)) * ∏ q ∈ P, (1 - (q : ℝ))) =
          ((-1 : ℝ) ^ P.card * ∏ q ∈ P, (1 - (q : ℝ))) *
            ((p : ℝ) - 1) := by ring
      rw [heq]
      exact mul_pos ih (by linarith)

/-- Every fixed finite insertion grade has its parity-predicted sign
throughout a sufficiently far primitive cone.  No fixed grade stabilizes the
one-prime negative payment against one further prime insertion. -/
theorem routeEPrimitiveBooleanTransport_eventual_parity_sign
    (a : ℝ) (P : Finset Nat.Primes) (ha : 0 < a) :
    ∀ᶠ b : ℝ in atTop,
      0 < (-1 : ℝ) ^ P.card * routeEPrimitiveBooleanTransport a b P := by
  have hlimit : 0 < (-1 : ℝ) ^ P.card *
      (a * ∏ p ∈ P, (1 - (p : ℝ))) := by
    have hp := signed_prime_survival_pos P
    nlinarith [mul_pos ha hp]
  have hscaled := (routeEPrimitiveBooleanTransport_scaled_limit a P).const_mul
    ((-1 : ℝ) ^ P.card)
  have hev := hscaled.eventually (eventually_gt_nhds hlimit)
  filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with b hpos hb
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
  by_contra h
  have hnon : (-1 : ℝ) ^ P.card * routeEPrimitiveBooleanTransport a b P ≤ 0 :=
    le_of_not_gt h
  have hmul := mul_nonpos_of_nonneg_of_nonpos hb2.le hnon
  nlinarith [hpos, hmul]

/-- The Boolean sign is the literal Möbius coefficient of the product of
distinct inserted prime labels. -/
private theorem moebius_prime_subset_product (S : Finset Nat.Primes) :
    (ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℝ) =
      (-1 : ℝ) ^ S.card := by
  let T : Finset ℕ := S.image (fun p : Nat.Primes => (p : ℕ))
  have hT : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact q.property
  have hcard : T.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
  have hprod : (∏ p ∈ T, p) = ∏ p ∈ S, (p : ℕ) := by
    dsimp [T]
    rw [Finset.prod_image]
    intro p hp q hq hpq
    exact Subtype.ext hpq
  have hmu := GibbsGas.moebius_prod_primes hT
  rw [hprod, hcard] at hmu
  exact_mod_cast hmu

/-- The exact source-signed numerator cube at a genuine prime denominator.
The numerator products are squarefree and their coefficients are actual
Möbius values, not freely selected signs. -/
def routeEPrimitiveMobiusBooleanTransport (q : ℕ) (P : Finset Nat.Primes) : ℝ :=
  ∑ S ∈ P.powerset,
    (ArithmeticFunction.moebius (∏ p ∈ S, (p : ℕ)) : ℝ) *
      (ArithmeticFunction.moebius q : ℝ) *
        routeEPrimitiveConeWeight (∏ p ∈ S, (p : ℝ)) q

theorem routeEPrimitiveMobiusBooleanTransport_eq_neg
    (q : ℕ) (P : Finset Nat.Primes) (hq : Nat.Prime q) :
    routeEPrimitiveMobiusBooleanTransport q P =
      -routeEPrimitiveBooleanTransport 1 q P := by
  have hqmu : ArithmeticFunction.moebius q = -1 :=
    ArithmeticFunction.moebius_apply_prime hq
  unfold routeEPrimitiveMobiusBooleanTransport routeEPrimitiveBooleanTransport
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  rw [moebius_prime_subset_product, hqmu]
  simp

/-- Arbitrarily far in the physical paired cone, the source-signed all-grade
cube has the parity-predicted sign at a genuine prime denominator. -/
theorem routeEPrimitiveMobiusBooleanTransport_arbitrarily_large_sign
    (P : Finset Nat.Primes) (N : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ N < q ∧
      2 * (∏ p ∈ P, (p : ℕ)) < q ∧
      0 < (-1 : ℝ) ^ (P.card + 1) *
        routeEPrimitiveMobiusBooleanTransport q P := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    (routeEPrimitiveBooleanTransport_eventual_parity_sign 1 P (by norm_num))
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let m : ℕ := max N (max (2 * ∏ p ∈ P, (p : ℕ)) n)
  obtain ⟨q, hq, hqprime⟩ := Nat.exists_infinite_primes (m + 1)
  have hN : N < q := by dsimp [m] at hq; omega
  have hcone : 2 * (∏ p ∈ P, (p : ℕ)) < q := by dsimp [m] at hq; omega
  have hnq : n < q := by dsimp [m] at hq; omega
  have hBq : B ≤ (q : ℝ) := by
    have hnqR : (n : ℝ) < q := by exact_mod_cast hnq
    exact le_of_lt (lt_trans hn hnqR)
  have hsign := hB q hBq
  refine ⟨q, hqprime, hN, hcone, ?_⟩
  rw [routeEPrimitiveMobiusBooleanTransport_eq_neg q P hqprime]
  simpa [pow_succ, mul_assoc] using hsign

/-! ## Physical-cone sign transition at fixed prime support -/

/-- The two-prime numerator cube with inserted primes two and three. -/
def routeEPrimitiveTwoThreeCube (b : ℝ) : ℝ :=
  routeEPrimitiveConeWeight 1 b - routeEPrimitiveConeWeight 2 b -
    routeEPrimitiveConeWeight 3 b + routeEPrimitiveConeWeight 6 b

private theorem routeEPrimitiveTwoThreeCube_scaled_limit :
    Tendsto (fun b : ℝ => b ^ 2 * routeEPrimitiveTwoThreeCube b) atTop (𝓝 2) := by
  have h := (((primitive_scaled_limit 1).sub (primitive_scaled_limit 2)).sub
    (primitive_scaled_limit 3)).add (primitive_scaled_limit 6)
  convert h using 1
  · funext b
    dsimp [routeEPrimitiveTwoThreeCube]
    ring
  · norm_num

/-- Literal Möbius-signed version of the same four physical primitive pairs. -/
def routeEPrimitiveTwoThreeSource (q : ℕ) : ℝ :=
  (ArithmeticFunction.moebius 1 : ℝ) *
    (ArithmeticFunction.moebius q : ℝ) * routeEPrimitiveConeWeight 1 q +
  (ArithmeticFunction.moebius 2 : ℝ) *
    (ArithmeticFunction.moebius q : ℝ) * routeEPrimitiveConeWeight 2 q +
  (ArithmeticFunction.moebius 3 : ℝ) *
    (ArithmeticFunction.moebius q : ℝ) * routeEPrimitiveConeWeight 3 q +
  (ArithmeticFunction.moebius 6 : ℝ) *
    (ArithmeticFunction.moebius q : ℝ) * routeEPrimitiveConeWeight 6 q

private theorem routeEPrimitiveTwoThreeSource_eq_neg (q : ℕ) (hq : Nat.Prime q) :
    routeEPrimitiveTwoThreeSource q = -routeEPrimitiveTwoThreeCube q := by
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)
  have hqmu : ArithmeticFunction.moebius q = -1 :=
    ArithmeticFunction.moebius_apply_prime hq
  have h6 : ArithmeticFunction.moebius 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      RHTower.Sieve.moebius_mul_of_coprime (by norm_num : Nat.Coprime 2 3), h2, h3]
    norm_num
  simp [routeEPrimitiveTwoThreeSource, routeEPrimitiveTwoThreeCube, h2, h3, h6, hqmu]
  ring

/-- At the first prime denominator strictly inside `2·6<q`, the complete
four-cell source cube is positive. -/
theorem routeEPrimitiveTwoThreeSource_near_cone_positive :
    2 * (6 : ℕ) < 13 ∧ Nat.Coprime 6 13 ∧
      0 < routeEPrimitiveTwoThreeSource 13 := by
  rw [routeEPrimitiveTwoThreeSource_eq_neg 13 (by norm_num : Nat.Prime 13)]
  norm_num [routeEPrimitiveTwoThreeCube, routeEPrimitiveConeWeight]

/-- At arbitrarily large genuine prime denominators, still in the same
paired cone, the identical literal source cube is negative.  Thus this local
source has a real cone-scale sign transition, not merely alternating signs
between different prime grades. -/
theorem routeEPrimitiveTwoThreeSource_arbitrarily_large_negative (N : ℕ) :
    ∃ q : ℕ, Nat.Prime q ∧ N < q ∧ 12 < q ∧
      routeEPrimitiveTwoThreeSource q < 0 := by
  have hev := routeEPrimitiveTwoThreeCube_scaled_limit.eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 hev
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let m : ℕ := max N (max 12 n)
  obtain ⟨q, hq, hqprime⟩ := Nat.exists_infinite_primes (m + 1)
  have hN : N < q := by dsimp [m] at hq; omega
  have hcone : 12 < q := by dsimp [m] at hq; omega
  have hnq : n < q := by dsimp [m] at hq; omega
  have hBq : B ≤ (q : ℝ) := by
    have hnqR : (n : ℝ) < q := by exact_mod_cast hnq
    exact le_of_lt (lt_trans hn hnqR)
  have hpos := hB q hBq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hcube : 0 < routeEPrimitiveTwoThreeCube q := by
    have hq2 := sq_pos_of_pos hqR
    by_contra h
    have hnon : routeEPrimitiveTwoThreeCube q ≤ 0 := le_of_not_gt h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hq2.le hnon]
  refine ⟨q, hqprime, hN, hcone, ?_⟩
  rw [routeEPrimitiveTwoThreeSource_eq_neg q hqprime]
  linarith

end
end RHTower
