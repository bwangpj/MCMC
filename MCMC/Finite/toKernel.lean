import Mathlib.Probability.Kernel.Invariant

namespace MCMC.Finite

open ProbabilityTheory MeasureTheory

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Convert a stochastic matrix to a Markov kernel on finite types -/
noncomputable def matrixToKernel (P : Matrix n n ℝ) (hP : IsStochastic P) :
    Kernel n n where
  val := fun i => Measure.ofFinset (fun j => P i j) (by simp [hP.2])
  property := sorry -- measurability proof

/-- Convert a probability vector to a probability measure on finite types -/
noncomputable def vecToMeasure (π : stdSimplex ℝ n) : Measure n :=
  Measure.ofFinset (fun i => π.val i) (by simp [π.2])

/-- Matrix stationarity is equivalent to kernel invariance -/
theorem isStationary_iff_invariant (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
    (hP : IsStochastic P) :
    IsStationary P π ↔
    Kernel.Invariant (matrixToKernel P hP) (vecToMeasure π) := by
  sorry -- prove equivalence

/-- Matrix reversibility is equivalent to kernel reversibility -/
theorem isReversible_iff_kernel_reversible (P : Matrix n n ℝ) (π : stdSimplex ℝ n)
    (hP : IsStochastic P) :
    IsReversible P π ↔
    Kernel.IsReversible (matrixToKernel P hP) (vecToMeasure π) := by
  sorry -- prove equivalence

/-- Use the kernel version to prove reversibility implies stationarity -/
theorem IsReversible.is_stationary' {P : Matrix n n ℝ} {π : stdSimplex ℝ n}
    (hP : IsStochastic P) (h_rev : IsReversible P π) :
    IsStationary P π := by
  rw [isStationary_iff_invariant P π hP]
  rw [isReversible_iff_kernel_reversible P π hP] at h_rev
  haveI : IsMarkovKernel (matrixToKernel P hP) := sorry
  exact h_rev.invariant

end MCMC.Finite
