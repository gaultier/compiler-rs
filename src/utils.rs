pub(crate) fn round_up(n: usize, rnd: usize) -> usize {
    (n + (rnd - 1)) & !(rnd - 1)
}
