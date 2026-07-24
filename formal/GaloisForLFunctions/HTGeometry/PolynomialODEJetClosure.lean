import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
# Polynomial ODE jet closure

Finite jets of a polynomial differential system form a closed differential algebra: products
become binomial convolutions.  This module exposes that connector and carries out the exact
eighth-jet elimination for the self-dual four-state theta system.

The result is independent of any theta realization.  A later RHTower module supplies the actual
theta-nullwert solution from source identities and thereby turns the formal closure into an
unconditional source theorem.
-/

open scoped BigOperators ContDiff

namespace HTGeometry

noncomputable section

set_option maxHeartbeats 2000000

/-- Binomial convolution of two scalar jet sequences. -/
def scalarJetConvolution (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1),
    n.choose i * a i * b (n - i)

/-- Jet of the constant function `1`. -/
def scalarJetUnit : ℕ → ℂ
  | 0 => 1
  | _ + 1 => 0

/-- Exact eighth-jet elimination for the self-dual theta modular ODE.

The four jet sequences correspond to

`H' = -H(p+Rz)/6`,
`z' = -R(1-z²)`,
`R' = -2R(p+Rz)/3`,
`p' = 3-p²/3+R²(3+z²)/12`,

with seam data `(H,z,R,p)=(M,0,R,0)`.  The conclusion is the sixth logarithmic
source combination for `Φ=(H''-H/4)/2`. -/
theorem modularThetaSixthSeamJetElimination
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
    let f : ℕ → ℂ :=
      fun n => (h (n + 2) - (1 / 4 : ℂ) * h n) / 2
    f 0 ^ 2 * f 6 - 15 * f 0 * f 2 * f 4 + 30 * f 2 ^ 3 =
      M ^ 3 / 131072 *
        (99 * (R ^ 2) ^ 6 + 12 * (R ^ 2) ^ 5 -
          3160 * (R ^ 2) ^ 4 - 544272 * (R ^ 2) ^ 3 -
          1446144 * (R ^ 2) ^ 2 - 1509120 * (R ^ 2) + 276480) := by
  have hh1 := hh 0
  have hz1 := hz 0
  have hr1 := hr 0
  have hp1 := hp 0
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0]
      at hh1 hz1 hr1 hp1
  ring_nf at hh1 hz1 hr1 hp1
  have hh2 := hh 1
  have hz2 := hz 1
  have hr2 := hr 1
  have hp2 := hp 1
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1] at hh2 hz2 hr2 hp2
  ring_nf at hh2 hz2 hr2 hp2
  have hh3 := hh 2
  have hz3 := hz 2
  have hr3 := hr 2
  have hp3 := hp 2
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2]
      at hh3 hz3 hr3 hp3
  ring_nf at hh3 hz3 hr3 hp3
  have hh4 := hh 3
  have hz4 := hz 3
  have hr4 := hr 3
  have hp4 := hp 3
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3] at hh4 hz4 hr4 hp4
  ring_nf at hh4 hz4 hr4 hp4
  have hh5 := hh 4
  have hz5 := hz 4
  have hr5 := hr 4
  have hp5 := hp 4
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4]
      at hh5 hz5 hr5 hp5
  ring_nf at hh5 hz5 hr5 hp5
  have hh6 := hh 5
  have hz6 := hz 5
  have hr6 := hr 5
  have hp6 := hp 5
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5] at hh6 hz6 hr6 hp6
  ring_nf at hh6 hz6 hr6 hp6
  have hh7 := hh 6
  have hz7 := hz 6
  have hr7 := hr 6
  have hp7 := hp 6
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6]
      at hh7 hz7 hr7 hp7
  ring_nf at hh7 hz7 hr7 hp7
  have hh8 := hh 7
  norm_num [scalarJetConvolution, scalarJetUnit,
    Finset.sum_range_succ, Nat.choose, hh0, hz0, hr0, hp0,
    hh1, hz1, hr1, hp1, hh2, hz2, hr2, hp2,
    hh3, hz3, hr3, hp3, hh4, hz4, hr4, hp4,
    hh5, hz5, hr5, hp5, hh6, hz6, hr6, hp6,
    hh7, hz7, hr7, hp7] at hh8
  ring_nf at hh8
  dsimp
  rw [hh0, hh2, hh4, hh6, hh8]
  ring

/-- Leibniz rule in the public jet-convolution coordinates. -/
theorem iteratedDeriv_mul_eq_scalarJetConvolution
    {f g : ℝ → ℂ} {n : ℕ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    iteratedDeriv n (f * g) x =
      ∑ i ∈ Finset.range (n + 1),
        n.choose i * iteratedDeriv i f x *
          iteratedDeriv (n - i) g x :=
  iteratedDeriv_mul hf hg

/-- Analytic-to-algebraic closure for any smooth solution of the self-dual theta ODE.
This theorem converts the four differential equations into jet convolutions and invokes
`modularThetaSixthSeamJetElimination`; callers need not expose any finite-jet premise. -/
theorem modularThetaSixthSeamClosure_of_ode
    (M R : ℂ) (h z r p : ℝ → ℂ)
    (hhc : ContDiff ℝ ∞ h) (hzc : ContDiff ℝ ∞ z)
    (hrc : ContDiff ℝ ∞ r) (hpc : ContDiff ℝ ∞ p)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh' : ∀ x, deriv h x =
      -(1 / 6 : ℂ) * (h x * (p x + r x * z x)))
    (hz' : ∀ x, deriv z x =
      -(r x * (1 - z x * z x)))
    (hr' : ∀ x, deriv r x =
      -(2 / 3 : ℂ) * (r x * (p x + r x * z x)))
    (hp' : ∀ x, deriv p x =
      3 - (1 / 3 : ℂ) * (p x * p x) +
        (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x))) :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) h 0 -
        (1 / 4 : ℂ) * iteratedDeriv n h 0) / 2
    f 0 ^ 2 * f 6 - 15 * f 0 * f 2 * f 4 + 30 * f 2 ^ 3 =
      M ^ 3 / 131072 *
        (99 * (R ^ 2) ^ 6 + 12 * (R ^ 2) ^ 5 -
          3160 * (R ^ 2) ^ 4 - 544272 * (R ^ 2) ^ 3 -
          1446144 * (R ^ 2) ^ 2 - 1509120 * (R ^ 2) + 276480) := by
  let jh : ℕ → ℂ := fun n => iteratedDeriv n h 0
  let jz : ℕ → ℂ := fun n => iteratedDeriv n z 0
  let jr : ℕ → ℂ := fun n => iteratedDeriv n r 0
  let jp : ℕ → ℂ := fun n => iteratedDeriv n p 0
  have hunit (n : ℕ) :
      iteratedDeriv n (fun _ : ℝ => (1 : ℂ)) 0 =
        scalarJetUnit n := by
    cases n <;> simp [scalarJetUnit, iteratedDeriv_const]
  have hconst3 (n : ℕ) :
      iteratedDeriv n (fun _ : ℝ => (3 : ℂ)) 0 =
        3 * scalarJetUnit n := by
    cases n <;> simp [scalarJetUnit, iteratedDeriv_const]
  have hmul (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f * g) 0 =
        scalarJetConvolution
          (fun k => iteratedDeriv k f 0)
          (fun k => iteratedDeriv k g 0) n := by
    exact iteratedDeriv_mul
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f + g) 0 =
        iteratedDeriv n f 0 + iteratedDeriv n g 0 := by
    exact iteratedDeriv_add
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f - g) 0 =
        iteratedDeriv n f 0 - iteratedDeriv n g 0 := by
    exact iteratedDeriv_sub
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have jh0 : jh 0 = M := by simpa [jh] using hh0
  have jz0 : jz 0 = 0 := by simpa [jz] using hz0
  have jr0 : jr 0 = R := by simpa [jr] using hr0
  have jp0 : jp 0 = 0 := by simpa [jp] using hp0
  have jhrec (n : ℕ) :
      jh (n + 1) =
        -(1 / 6 : ℂ) *
          scalarJetConvolution jh
            (fun k => jp k + scalarJetConvolution jr jz k) n := by
    simp only [jh, jp, jr, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv h = fun x =>
        -(1 / 6 : ℂ) * (h x * (p x + r x * z x)) :=
      funext hh'
    rw [heq]
    rw [iteratedDeriv_const_mul (-(1 / 6 : ℂ))
      ((hhc.mul (hpc.add (hrc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change -(1 / 6 : ℂ) *
        iteratedDeriv n (h * (p + r * z)) 0 = _
    rw [hmul h (p + r * z) hhc
      (hpc.add (hrc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ => -(1 / 6 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hadd p (r * z) hpc (hrc.mul hzc)]
    rw [hmul r z hrc hzc]
    rfl
  have jzrec (n : ℕ) :
      jz (n + 1) =
        -scalarJetConvolution jr
          (fun k => scalarJetUnit k -
            scalarJetConvolution jz jz k) n := by
    simp only [jz, jr]
    rw [iteratedDeriv_succ']
    have heq : deriv z = fun x =>
        (-1 : ℂ) * (r x * (1 - z x * z x)) := by
      funext x
      rw [hz']
      ring
    rw [heq]
    rw [iteratedDeriv_const_mul (-1 : ℂ)
      ((hrc.mul (contDiff_const.sub (hzc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change (-1 : ℂ) *
        iteratedDeriv n (r * ((fun _ : ℝ => (1 : ℂ)) - z * z)) 0 = _
    rw [hmul r ((fun _ : ℝ => (1 : ℂ)) - z * z) hrc
      (contDiff_const.sub (hzc.mul hzc)) n]
    unfold scalarJetConvolution
    rw [neg_one_mul]
    apply congrArg (fun q : ℂ => -q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hsub (fun _ : ℝ => (1 : ℂ)) (z * z)
      contDiff_const (hzc.mul hzc), hunit]
    rw [hmul z z hzc hzc]
    rfl
  have jrrec (n : ℕ) :
      jr (n + 1) =
        -(2 / 3 : ℂ) *
          scalarJetConvolution jr
            (fun k => jp k + scalarJetConvolution jr jz k) n := by
    simp only [jr, jp, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv r = fun x =>
        -(2 / 3 : ℂ) * (r x * (p x + r x * z x)) :=
      funext hr'
    rw [heq]
    rw [iteratedDeriv_const_mul (-(2 / 3 : ℂ))
      ((hrc.mul (hpc.add (hrc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change -(2 / 3 : ℂ) *
        iteratedDeriv n (r * (p + r * z)) 0 = _
    rw [hmul r (p + r * z) hrc
      (hpc.add (hrc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ => -(2 / 3 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hadd p (r * z) hpc (hrc.mul hzc)]
    rw [hmul r z hrc hzc]
    rfl
  have jprec (n : ℕ) :
      jp (n + 1) =
        3 * scalarJetUnit n -
          (1 / 3 : ℂ) * scalarJetConvolution jp jp n +
          (1 / 12 : ℂ) *
            scalarJetConvolution (scalarJetConvolution jr jr)
              (fun k => 3 * scalarJetUnit k +
                scalarJetConvolution jz jz k) n := by
    simp only [jp, jr, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv p = fun x =>
        3 - (1 / 3 : ℂ) * (p x * p x) +
          (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x)) :=
      funext hp'
    rw [heq]
    change iteratedDeriv n
        ((fun x : ℝ => (3 : ℂ) - (1 / 3 : ℂ) * (p x * p x)) +
          fun x : ℝ =>
            (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [iteratedDeriv_add
      ((contDiff_const.sub
        (contDiff_const.mul (hpc.mul hpc))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      ((contDiff_const.mul ((hrc.mul hrc).mul
        (contDiff_const.add (hzc.mul hzc)))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      iteratedDeriv n
          ((fun _ : ℝ => (3 : ℂ)) -
            fun x => (1 / 3 : ℂ) * (p x * p x)) 0 +
        iteratedDeriv n
          (fun x => (1 / 12 : ℂ) *
            ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [iteratedDeriv_sub contDiffAt_const
      ((contDiff_const.mul (hpc.mul hpc)).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    rw [hconst3]
    rw [iteratedDeriv_const_mul (1 / 3 : ℂ)
      ((hpc.mul hpc).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) * iteratedDeriv n (p * p) 0 +
        iteratedDeriv n
          (fun x => (1 / 12 : ℂ) *
            ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [hmul p p hpc hpc]
    rw [iteratedDeriv_const_mul (1 / 12 : ℂ)
      (((hrc.mul hrc).mul
        (contDiff_const.add (hzc.mul hzc))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) *
            scalarJetConvolution
              (fun k => iteratedDeriv k p 0)
              (fun k => iteratedDeriv k p 0) n +
        (1 / 12 : ℂ) *
          iteratedDeriv n
            ((r * r) * ((fun _ : ℝ => (3 : ℂ)) + z * z)) 0 = _
    rw [hmul (r * r) ((fun _ : ℝ => (3 : ℂ)) + z * z)
      (hrc.mul hrc) (contDiff_const.add (hzc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ =>
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) *
            scalarJetConvolution
              (fun k => iteratedDeriv k p 0)
              (fun k => iteratedDeriv k p 0) n +
        (1 / 12 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    · simp only
      rw [hmul r r hrc hrc]
      rfl
    · simp only
      rw [hadd (fun _ : ℝ => (3 : ℂ)) (z * z)
            contDiff_const (hzc.mul hzc),
          hconst3, hmul z z hzc hzc]
      rfl
  exact modularThetaSixthSeamJetElimination M R jh jz jr jp
    jh0 jz0 jr0 jp0 jhrec jzrec jrrec jprec

end

end HTGeometry
