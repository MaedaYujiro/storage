use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;

#[derive(Debug, Clone)]
pub struct Graph {
    pub num_vertices: usize,
    pub num_edges: usize,
    pub adj_list: Vec<Vec<usize>>,
}

impl Graph {
    pub fn new(num_vertices: usize) -> Self {
        Graph {
            num_vertices,
            num_edges: 0,
            adj_list: vec![Vec::new(); num_vertices],
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize) {
        if u < self.num_vertices && v < self.num_vertices && u != v {
            if !self.adj_list[u].contains(&v) {
                self.adj_list[u].push(v);
                self.adj_list[v].push(u);
                self.num_edges += 1;
            }
        }
    }

    pub fn from_dimacs<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let mut graph: Option<Graph> = None;

        for line in reader.lines() {
            let line = line?;
            let line = line.trim();

            if line.is_empty() {
                continue;
            }

            let first_char = line.chars().next().unwrap();

            match first_char {
                'c' => {
                    // Comment line, skip
                    continue;
                }
                'p' => {
                    // Problem line: p edge <num_vertices> <num_edges>
                    let parts: Vec<&str> = line.split_whitespace().collect();
                    if parts.len() >= 4 && parts[1] == "edge" {
                        let num_vertices: usize = parts[2].parse()?;
                        graph = Some(Graph::new(num_vertices));
                    }
                }
                'e' => {
                    // Edge line: e <u> <v>
                    if let Some(ref mut g) = graph {
                        let parts: Vec<&str> = line.split_whitespace().collect();
                        if parts.len() >= 3 {
                            let u: usize = parts[1].parse()?;
                            let v: usize = parts[2].parse()?;
                            // DIMACS uses 1-indexed vertices, convert to 0-indexed
                            g.add_edge(u - 1, v - 1);
                        }
                    }
                }
                _ => {
                    // Unknown line type, skip
                    continue;
                }
            }
        }

        graph.ok_or_else(|| "No problem line found in DIMACS file".into())
    }

    pub fn degree(&self, v: usize) -> usize {
        self.adj_list[v].len()
    }

    pub fn max_degree(&self) -> usize {
        (0..self.num_vertices).map(|v| self.degree(v)).max().unwrap_or(0)
    }

    pub fn neighbors(&self, v: usize) -> &[usize] {
        &self.adj_list[v]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_new_creates_empty_graph() {
        let g = Graph::new(5);
        assert_eq!(g.num_vertices, 5);
        assert_eq!(g.num_edges, 0);
        assert_eq!(g.adj_list.len(), 5);
        for neighbors in &g.adj_list {
            assert!(neighbors.is_empty());
        }
    }

    #[test]
    fn test_new_zero_vertices() {
        let g = Graph::new(0);
        assert_eq!(g.num_vertices, 0);
        assert_eq!(g.num_edges, 0);
        assert!(g.adj_list.is_empty());
    }

    #[test]
    fn test_add_edge_basic() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        assert_eq!(g.num_edges, 1);
        assert!(g.adj_list[0].contains(&1));
        assert!(g.adj_list[1].contains(&0));
    }

    #[test]
    fn test_add_edge_no_self_loop() {
        let mut g = Graph::new(3);
        g.add_edge(1, 1);
        assert_eq!(g.num_edges, 0);
        assert!(g.adj_list[1].is_empty());
    }

    #[test]
    fn test_add_edge_no_duplicate() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(0, 1);
        g.add_edge(1, 0);
        assert_eq!(g.num_edges, 1);
        assert_eq!(g.adj_list[0].len(), 1);
        assert_eq!(g.adj_list[1].len(), 1);
    }

    #[test]
    fn test_add_edge_out_of_bounds() {
        let mut g = Graph::new(3);
        g.add_edge(0, 5);
        g.add_edge(5, 0);
        assert_eq!(g.num_edges, 0);
    }

    #[test]
    fn test_degree() {
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(0, 2);
        g.add_edge(0, 3);
        assert_eq!(g.degree(0), 3);
        assert_eq!(g.degree(1), 1);
        assert_eq!(g.degree(2), 1);
        assert_eq!(g.degree(3), 1);
    }

    #[test]
    fn test_max_degree() {
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(0, 2);
        g.add_edge(0, 3);
        g.add_edge(1, 2);
        assert_eq!(g.max_degree(), 3);
    }

    #[test]
    fn test_max_degree_empty_graph() {
        let g = Graph::new(5);
        assert_eq!(g.max_degree(), 0);
    }

    #[test]
    fn test_max_degree_zero_vertices() {
        let g = Graph::new(0);
        assert_eq!(g.max_degree(), 0);
    }

    #[test]
    fn test_neighbors() {
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(0, 2);
        let neighbors = g.neighbors(0);
        assert_eq!(neighbors.len(), 2);
        assert!(neighbors.contains(&1));
        assert!(neighbors.contains(&2));
    }

    #[test]
    fn test_from_dimacs_basic() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "c test graph").unwrap();
        writeln!(file, "p edge 3 2").unwrap();
        writeln!(file, "e 1 2").unwrap();
        writeln!(file, "e 2 3").unwrap();

        let g = Graph::from_dimacs(file.path()).unwrap();
        assert_eq!(g.num_vertices, 3);
        assert_eq!(g.num_edges, 2);
        assert!(g.adj_list[0].contains(&1));
        assert!(g.adj_list[1].contains(&0));
        assert!(g.adj_list[1].contains(&2));
        assert!(g.adj_list[2].contains(&1));
    }

    #[test]
    fn test_from_dimacs_with_comments() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "c comment 1").unwrap();
        writeln!(file, "c comment 2").unwrap();
        writeln!(file, "p edge 2 1").unwrap();
        writeln!(file, "c another comment").unwrap();
        writeln!(file, "e 1 2").unwrap();

        let g = Graph::from_dimacs(file.path()).unwrap();
        assert_eq!(g.num_vertices, 2);
        assert_eq!(g.num_edges, 1);
    }

    #[test]
    fn test_from_dimacs_empty_lines() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "p edge 2 1").unwrap();
        writeln!(file, "").unwrap();
        writeln!(file, "e 1 2").unwrap();
        writeln!(file, "").unwrap();

        let g = Graph::from_dimacs(file.path()).unwrap();
        assert_eq!(g.num_vertices, 2);
        assert_eq!(g.num_edges, 1);
    }

    #[test]
    fn test_from_dimacs_no_problem_line() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "c only comments").unwrap();
        writeln!(file, "e 1 2").unwrap();

        let result = Graph::from_dimacs(file.path());
        assert!(result.is_err());
    }

    #[test]
    fn test_from_dimacs_file_not_found() {
        let result = Graph::from_dimacs("/nonexistent/path/to/file.col");
        assert!(result.is_err());
    }

    #[test]
    fn test_from_dimacs_duplicate_edges() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "p edge 3 4").unwrap();
        writeln!(file, "e 1 2").unwrap();
        writeln!(file, "e 2 1").unwrap();
        writeln!(file, "e 1 2").unwrap();

        let g = Graph::from_dimacs(file.path()).unwrap();
        assert_eq!(g.num_edges, 1);
    }
}
