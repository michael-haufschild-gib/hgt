import GaloisForLFunctions.RHTower.RouteEComponentHistoryGibbsParity

/-!
# Route E literal prime-activation complete-histogram aperture no-go

Complete component-histogram cells solve Route E's equal-product collision problem, but physical
shell conditioning is not free.  A singleton binary cell contains the extreme history putting
every active component in one replica and its swap putting every active component in another.
At the first replica these histories expose the all-active and all-inactive products.

If each active value is at least twice its inactive value—as for literal prime activation—then a
nonempty component family changes the product by at least two.  A physical aperture with
`3 H < X` has multiplicative width strictly below two.  Hence no nonempty literal-prime complete
histogram cell fits wholly inside that aperture.

This kills the direct chain

`literal prime activation → complete histogram cell → Gibbs parity comparison → Route E → RH`.

The sharp survivor must use near-unit or mixed-orientation/log-balanced component ratios, or give
up the complete cell and control a product-shell-conditioned incomplete cell.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Singleton binary history with every active component placed in the first replica. -/
def routeEPrimeActivationSeed (n M : ℕ) :
    RouteEComponentHistory (fun _ : Fin n => Bool) (M + 2) :=
  fun r _ => if r = 0 then true else false

/-- Closed route class: a nonempty literal-prime activation family whose complete singleton
component-histogram cell remains inside one narrow physical aperture.  `M + 2` records that at
least two replica slots are present, and the factor-two law includes every ordinary prime. -/
def RouteEPrimeActivationCompleteHistogramApertureCell : Prop :=
  ∃ (n M : ℕ) (value : Fin n → Bool → ℝ) (X H : ℝ),
    0 < n ∧
    0 < X ∧
    0 ≤ H ∧
    3 * H < X ∧
    (∀ c, 0 < value c false ∧ 2 * value c false ≤ value c true) ∧
    let seed := routeEPrimeActivationSeed n M
    ∀ x ∈ routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed),
      ∀ r, routeEComponentSlotReceiver (fun _ : Fin n => Bool) value x r ∈
        Set.Icc (X - H) (X + H)

private theorem routeEPrimeActivationSeed_mem_cell (n M : ℕ) :
    routeEPrimeActivationSeed n M ∈
      routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool)
          (routeEPrimeActivationSeed n M)) := by
  classical
  simp [routeEComponentHistogramCell, routeEComponentHistoryLabel]

private theorem routeEPrimeActivationSeed_receiver_zero
    (n M : ℕ) (value : Fin n → Bool → ℝ) :
    routeEComponentSlotReceiver (fun _ : Fin n => Bool) value
        (routeEPrimeActivationSeed n M) 0 =
      ∏ c, value c true := by
  classical
  simp [routeEComponentSlotReceiver, routeEPrimeActivationSeed]

private theorem routeEPrimeActivationSeed_swap_receiver_zero
    (n M : ℕ) (value : Fin n → Bool → ℝ) :
    routeEComponentSlotReceiver (fun _ : Fin n => Bool) value
        (routeEComponentHistoryAnchorSwap (fun _ : Fin n => Bool)
          (0 : Fin (M + 2)) (1 : Fin (M + 2))
          (routeEPrimeActivationSeed n M)) 0 =
      ∏ c, value c false := by
  classical
  simp [routeEComponentSlotReceiver, routeEPrimeActivationSeed,
    routeEComponentHistoryAnchorSwap]

/-- Sharp positive boundary exposed by the complete-cell obstruction.  If a complete singleton
component-histogram cell lies in one positive physical aperture, then the ratio between its
all-active and all-inactive products cannot exceed the aperture's multiplicative width.

Unlike the factor-two no-go below, this theorem applies to arbitrary positive component values.
It isolates the exact surviving design constraint for Route E: complete cells require globally
near-unit or compensating activation ratios. -/
def RouteECompleteHistogramActivationRatioBound : Prop :=
  ∀ (n M : ℕ) (value : Fin n → Bool → ℝ) (X H : ℝ),
    0 < X →
    0 ≤ H →
    H < X →
    (∀ c, 0 < value c false) →
    (∀ x ∈ routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool)
          (routeEPrimeActivationSeed n M)),
      ∀ r, routeEComponentSlotReceiver (fun _ : Fin n => Bool) value x r ∈
        Set.Icc (X - H) (X + H)) →
    (∏ c, value c true) / (∏ c, value c false) ≤ (X + H) / (X - H)

/-- Every complete singleton component-histogram cell in a positive physical aperture obeys the
sharp total activation-ratio bound imposed by the two extreme histories.  This is a closed,
premise-free universal proposition. -/
theorem routeE_completeHistogram_activationRatioBound :
    RouteECompleteHistogramActivationRatioBound := by
  intro n M value X H hX hH hHX hvalue haperture
  let seed := routeEPrimeActivationSeed n M
  let swapped := routeEComponentHistoryAnchorSwap (fun _ : Fin n => Bool)
    (0 : Fin (M + 2)) (1 : Fin (M + 2)) seed
  have hseed : seed ∈
      routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed) := by
    exact routeEPrimeActivationSeed_mem_cell n M
  have hswapped : swapped ∈
      routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed) := by
    dsimp [swapped]
    exact (routeEComponentHistoryAnchorSwap_mem_cell_iff
      (fun _ : Fin n => Bool)
      (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed)
      (0 : Fin (M + 2)) (1 : Fin (M + 2)) seed).2 hseed
  have hactive := haperture seed hseed (0 : Fin (M + 2))
  have hbase := haperture swapped hswapped (0 : Fin (M + 2))
  rw [routeEPrimeActivationSeed_receiver_zero] at hactive
  change routeEComponentSlotReceiver (fun _ : Fin n => Bool) value
      (routeEComponentHistoryAnchorSwap (fun _ : Fin n => Bool)
        (0 : Fin (M + 2)) (1 : Fin (M + 2))
        (routeEPrimeActivationSeed n M)) 0 ∈ Set.Icc (X - H) (X + H) at hbase
  rw [routeEPrimeActivationSeed_swap_receiver_zero] at hbase
  have hbasePos : 0 < ∏ c : Fin n, value c false :=
    Finset.prod_pos fun c hc => hvalue c
  calc
    (∏ c, value c true) / (∏ c, value c false) ≤
        (X + H) / (∏ c, value c false) :=
      div_le_div_of_nonneg_right hactive.2 hbasePos.le
    _ ≤ (X + H) / (X - H) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) hbase.1

/-- **Route E route-class kill.** No nonempty complete singleton component-histogram cell built
from literal factor-two prime activations can remain in a physical aperture narrower than the
factor-two jump.  The theorem is premise-free: all candidate data are quantified inside the
closed route class. -/
theorem not_RouteEPrimeActivationCompleteHistogramApertureCell :
    ¬ RouteEPrimeActivationCompleteHistogramApertureCell := by
  rintro ⟨n, M, value, X, H, hn, hX, hH, hthin, hvalue, haperture⟩
  let seed := routeEPrimeActivationSeed n M
  let swapped := routeEComponentHistoryAnchorSwap (fun _ : Fin n => Bool)
    (0 : Fin (M + 2)) (1 : Fin (M + 2)) seed
  have hseed : seed ∈
      routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed) := by
    exact routeEPrimeActivationSeed_mem_cell n M
  have hswapped : swapped ∈
      routeEComponentHistogramCell (fun _ : Fin n => Bool) (M + 2)
        (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed) := by
    dsimp [swapped]
    exact (routeEComponentHistoryAnchorSwap_mem_cell_iff
      (fun _ : Fin n => Bool)
      (routeEComponentHistoryLabel (fun _ : Fin n => Bool) seed)
      (0 : Fin (M + 2)) (1 : Fin (M + 2)) seed).2 hseed
  have hactive := haperture seed hseed (0 : Fin (M + 2))
  have hbase := haperture swapped hswapped (0 : Fin (M + 2))
  rw [routeEPrimeActivationSeed_receiver_zero] at hactive
  change routeEComponentSlotReceiver (fun _ : Fin n => Bool) value
      (routeEComponentHistoryAnchorSwap (fun _ : Fin n => Bool)
        (0 : Fin (M + 2)) (1 : Fin (M + 2))
        (routeEPrimeActivationSeed n M)) 0 ∈ Set.Icc (X - H) (X + H) at hbase
  rw [routeEPrimeActivationSeed_swap_receiver_zero] at hbase
  have hproduct : (∏ c : Fin n, 2 * value c false) ≤
      ∏ c : Fin n, value c true := by
    apply Finset.prod_le_prod
    · intro c hc
      exact mul_nonneg (by norm_num) (hvalue c).1.le
    · intro c hc
      exact (hvalue c).2
  have hproduct' : (2 : ℝ) ^ n * (∏ c : Fin n, value c false) ≤
      ∏ c : Fin n, value c true := by
    simpa [Finset.prod_mul_distrib] using hproduct
  have hpower : (2 : ℝ) ≤ 2 ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [pow_succ]
    have hk : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    nlinarith
  have hbasePos : 0 < ∏ c : Fin n, value c false :=
    Finset.prod_pos fun c hc => (hvalue c).1
  have hdouble : 2 * (∏ c : Fin n, value c false) ≤
      ∏ c : Fin n, value c true :=
    (mul_le_mul_of_nonneg_right hpower hbasePos.le).trans hproduct'
  have hbaseLower : X - H ≤ ∏ c : Fin n, value c false := hbase.1
  have hactiveUpper : ∏ c : Fin n, value c true ≤ X + H := hactive.2
  nlinarith

end

end RHTower
