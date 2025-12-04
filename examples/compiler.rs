use compiler_rs_lib::{ast::Parser, lex::Lexer};

fn main() {
    let file_name = std::env::args().skip(1).next().unwrap();
    let file_content = std::fs::read_to_string(file_name).unwrap();

    let mut lexer = Lexer::new();
    lexer.lex(&file_content);

    println!("--- Lex ---");
    println!("tokens: {:#?}", &lexer.tokens);

    let mut parser = Parser::new(&file_content, &lexer);
    parser.parse();

    println!("--- Parse ---");
    println!("nodes: {:#?}", &parser.nodes);
    for err in &lexer.errors {
        err.write(&mut std::io::stderr(), &file_content).unwrap();
    }
}
